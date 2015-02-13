#! /usr/bin/perl 

#
# Copyleft 2015 PALS,
#     contact Simon Hieu Mai <master.simon21@yahoo.com>
# Copyleft 2014 Jon Scott <mr.jonathon.scott@gmail.com> 
# Copyleft 2014 Mark Cooper <mark.c.cooper@outlook.com> 
# Copyright 2012-2013 Midwest Consortium for Library Services
# Copyright 2013 Calvin College
#     contact Dan Wells <dbw2@calvin.edu>
# Copyright 2013 Traverse Area District Library,
#     contact Jeff Godin <jgodin@tadl.org>
#
#
# This code incorporates code (with modifications) from issa, "a small
# command-line client to OpenILS/Evergreen". issa is licensed GPLv2 or (at your
# option) any later version of the GPL.
#
# issa is copyright:
#
# Copyright 2011 Jason J.A. Stephenson <jason@sigio.com>
# Portions Copyright 2012 Merrimack Valley Library Consortium
# <jstephenson@mvlc.org>
#
#
# This file is part of iNCIPit
#
# iNCIPit is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#
# iNCIPit is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with iNCIPit. If not, see <http://www.gnu.org/licenses/>.

use warnings;
use XML::LibXML;
use CGI::XMLPost;
use HTML::Entities;
use CGI::Carp;
use XML::XPath;
use OpenSRF::System;
use OpenSRF::Utils::SettingsClient;
use Digest::MD5 qw/md5_hex/;
use OpenILS::Utils::Fieldmapper;
use OpenILS::Utils::CStoreEditor qw/:funcs/;
use OpenILS::Const qw/:const/;
use Scalar::Util qw(reftype blessed);
use MARC::Record;
use MARC::Field;
use MARC::File::XML;
use POSIX qw/strftime/;
use DateTime;

use OpenILS::SIP::Item;
use OpenILS::SIP::Patron;

use URI::Escape;
use Data::Dumper;

use Time::HiRes qw(usleep nanosleep);

my $U = "OpenILS::Application::AppUtils";

my $xmlpost = CGI::XMLPost->new();
my $xml     = $xmlpost->data();

# log posted data
# XXX: posted ncip message log filename should be in config.
open POST_DATA, ">>post_data.txt";
print POST_DATA "$xml\n";
close POST_DATA;

# read in last xml request
# XXX: just the most recently posted ncip message filename should be in config.
{
    local $/ = undef;
    if (open FILE, "last_post.txt") {
        binmode FILE;
        $prev_xml = <FILE>;
        close FILE;
    } else {
        # poor man's creat.
        (open(FILE, ">last_post.txt") && close(FILE))
            or die "Couldn't create file: $!";
    }
}

# uncomment this to prevent duplicating
# fail as gracefully as possible if repeat post has occured
#if ( $xml eq $prev_xml ) {
#    fail("DUPLICATE NCIP REQUEST POSTED!");
#}

# save just the last post in order to test diff on the next request
# XXX: just the most recently posted ncip message filename should be in config.
open LAST_POST_DATA, ">last_post.txt";
print LAST_POST_DATA $xml;
close LAST_POST_DATA;

# initialize the parser
my $parser = new XML::LibXML;
my $doc = $parser->load_xml( string => $xml );

my %session = login();

# Setup our SIGALRM handler.
$SIG{'ALRM'} = \&logout;

# The original iNCIPit supports NCIP version 1.0
# Simon (PALS) updated/modified 5 below messages to support NCIP version 2.0
# They are: RequestItem, CheckOutItem, CheckInItem, AcceptItem, and CancelRequestItem
# Note: The rest of these messages are still working for NCIP version 1.0. 
if ( defined( $session{authtoken} ) ) {
    $doc->exists('/NCIPMessage/LookupUser')           ? lookupUser()       : (	
    $doc->exists('/NCIPMessage/ItemRequested')        ? item_request()     : (
    $doc->exists('/ns1:NCIPMessage/ns1:RequestItem')        ? request_item()     : (    
    $doc->exists('/NCIPMessage/ItemShipped')          ? item_shipped()     : (
    $doc->exists('/NCIPMessage/ItemCheckedOut')       ? item_checked_out() : (
    $doc->exists('/ns1:NCIPMessage/ns1:CheckOutItem')         ? check_out_item()   : (	
    $doc->exists('/NCIPMessage/ItemCheckedIn')        ? item_checked_in()  : (
    $doc->exists('/ns1:NCIPMessage/ns1:CheckInItem')          ? check_in_item()    : (	
    $doc->exists('/NCIPMessage/ItemReceived')         ? item_received()    : (
    $doc->exists('/ns1:NCIPMessage/ns1:AcceptItem')           ? accept_item()      : (	
    $doc->exists('/NCIPMessage/ItemRequestCancelled') ? item_cancelled()   : (	
    $doc->exists('/ns1:NCIPMessage/ns1:CancelRequestItem') ? cancel_request_item()   : (  
    $doc->exists('/NCIPMessage/ItemRenewed')          ? item_renew()       : (
    fail("UNKNOWN NCIPMessage")
    )))))))))))));

    # Clear any SIGALRM timers.
    alarm(0);
    logout();
} else {
    fail("Unable to perform action : Unknown Service Request");
}

sub logit {
    my ( $msg, $func, $more_info ) = @_;
    open RESP_DATA, ">>resp_data.txt";
    print RESP_DATA $msg;
    print RESP_DATA $more_info unless !$more_info;
    close RESP_DATA;
    print $msg || fail($func);
}

sub staff_log {
    my ( $taiv, $faiv, $more_info ) = @_;
    my $now = localtime();
    open STAFF_LOG, ">>staff_data.csv";
    print STAFF_LOG "$now, $faiv, $taiv, $more_info\n";
    close STAFF_LOG;
}

sub item_renew {
    my $faidSchemeX = $doc->findvalue('/NCIPMessage/ItemRenewed/InitiationHeader/FromAgencyId/UniqueAgencyId/Scheme');
    my $faidScheme = HTML::Entities::encode($faidSchemeX);
    my $faidValue  = $doc->find('/NCIPMessage/ItemRenewed/InitiationHeader/FromAgencyId/UniqueAgencyId/Value');
    my $taidSchemeX = $doc->findvalue('/NCIPMessage/ItemRenewed/InitiationHeader/ToAgencyId/UniqueAgencyId/Scheme');
    my $taidScheme = HTML::Entities::encode($taidSchemeX);
    my $taidValue  = $doc->find('/NCIPMessage/ItemRenewed/InitiationHeader/ToAgencyId/UniqueAgencyId/Value');

    my $pid = $doc->findvalue('/NCIPMessage/ItemRenewed/UniqueUserId/UserIdentifierValue');
    my $visid = $doc->findvalue('/NCIPMessage/ItemRenewed/ItemOptionalFields/ItemDescription/VisibleItemId/VisibleItemIdentifier') . $faidValue;
    my $due_date = $doc->findvalue('/NCIPMessage/ItemRenewed/DateDue');

    my $r = renewal( $visid, $due_date );

    my $hd = <<ITEMRENEWAL;
Content-type: text/xml


<!DOCTYPE NCIPMessage PUBLIC "-//NISO//NCIP DTD Version 1.0//EN" "http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
<NCIPMessage version="http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
    <ItemRenewedResponse>
        <ResponseHeader>
            <FromAgencyId>
                <UniqueAgencyId>
                    <Scheme>$faidScheme</Scheme>
                    <Value>$faidValue</Value>
                </UniqueAgencyId>
            </FromAgencyId>
            <ToAgencyId>
                <UniqueAgencyId>
                    <Scheme>$taidScheme</Scheme>
                    <Value>$taidValue</Value>
                </UniqueAgencyId>
            </ToAgencyId>
        </ResponseHeader>
        <UniqueItemId>
            <ItemIdentifierValue datatype="string">$visid</ItemIdentifierValue>
        </UniqueItemId>
    </ItemRenewedResponse>
</NCIPMessage> 

ITEMRENEWAL

    my $more_info = <<MOREINFO;

VISID             = $visid
Desired Due Date     = $due_date

MOREINFO

    logit( $hd, ( caller(0) )[3], $more_info );
    staff_log( $taidValue, $faidValue,
            "ItemRenewal -> Patronid : "
          . $pid
          . " | Visid : "
          . $visid
          . " | Due Date : "
          . $due_date );
}

sub accept_item {
    my $faidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:InitiationHeader/ns1:FromAgencyId/ns1:AgencyId');
    my $taidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:InitiationHeader/ns1:ToAgencyId/ns1:AgencyId');
    my $visid = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:ItemId/ns1:ItemIdentifierValue');  # . $faidValue;
    my $aidValue = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:RequestId/ns1:AgencyId');
    my $request_id = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:RequestId/ns1:RequestIdentifierValue') || "unknown";
    my $patron = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:UserId/ns1:UserIdentifierValue');
    my $barcode = $visid; #barcode from MIT
    my $author = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:ItemOptionalFields/ns1:BibliographicDescription/ns1:Author');
    my $title = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:ItemOptionalFields/ns1:BibliographicDescription/ns1:Title');
    my $callnumber = $request_id;
    my $medium_type = $doc->findvalue('/ns1:NCIPMessage/ns1:AcceptItem/ns1:ItemOptionalFields/ns1:BibliographicDescription/ns1:MediumType');

    my $r = "default error checking response";

# Simon 2014/11/13: Add "ILL: " as the preface to the tite/245 field                                                                                                                                                                   
    $title = "ILL: " . $title; 
    my $copy_status_id = 101;    # XXX CUSTOMIZATION NEEDED XXX # INN-Reach Loan Requested - local configured status
# we want our custom status to be then end result, so create the copy with status of "Available, then hold it, then update the status
    $r = create_copy( $title, $callnumber, $barcode, 0, $medium_type );
    my $copy = copy_from_barcode($barcode);
    fail( $copy->{textcode} . " $visid" ) unless ( blessed $copy);
    my $r2   = place_hold('C', $copy->id, $patron, $taidValue);

    my $hd = <<ACCEPTITEM;
Content-type: text/xml


<ns1:NCIPMessage ns1:version="http://www.niso.org/ncip/v2_0/imp1/xsd/ncip_v2_0.xsd" xmlns:ns1="http://www.niso.org/2008/ncip" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:schemaLocation="http://www.niso.org/2008/ncip ncip_v2_0.xsd">
  <ns1:AcceptItemResponse>
     <ns1:RequestId>
        <ns1:AgencyId ns1:Scheme="localhost/ncip/v1/schemes/agencies/1">$aidValue</ns1:AgencyId>
        <ns1:RequestIdentifierValue>$request_id</ns1:RequestIdentifierValue>
     </ns1:RequestId>
  </ns1:AcceptItemResponse>
</ns1:NCIPMessage>


ACCEPTITEM

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
        "AcceptItem -> Request Id : " . $request_id . " | Patron Id : " . $patron . " | Visible Id :" . $visid );
}

sub item_received {
    my $faidValue = $doc->find('/NCIPMessage/ItemReceived/InitiationHeader/FromAgencyId/UniqueAgencyId/Value');
    my $visid = $doc->findvalue('/NCIPMessage/ItemReceived/ItemOptionalFields/ItemDescription/VisibleItemId/VisibleItemIdentifier') . $faidValue;
    my $copy = copy_from_barcode($visid);
    fail( $copy->{textcode} . " $visid" ) unless ( blessed $copy);
    my $r1 = checkin($visid) if ( $copy->status == OILS_COPY_STATUS_CHECKED_OUT ); # checkin the item before delete if ItemCheckedIn step was skipped
    my $r2 = delete_copy($copy);

    my $hd = <<ITEMRECEIVED;
Content-type: text/xml


<!DOCTYPE NCIPMessage PUBLIC "-//NISO//NCIP DTD Version 1.0//EN" "http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
<NCIPMessage version="http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
    <ItemReceivedResponse>
        <ResponseHeader>
            <FromAgencyId>
                <UniqueAgencyId>
                    <Scheme>$faidScheme</Scheme>
                    <Value>$faidValue</Value>
                </UniqueAgencyId>
            </FromAgencyId>
            <ToAgencyId>
                <UniqueAgencyId>
                    <Scheme>$taidScheme</Scheme>
                    <Value>$taidValue</Value>
                </UniqueAgencyId>
            </ToAgencyId>
        </ResponseHeader>
        <UniqueItemId>
            <ItemIdentifierValue datatype="string">$visid</ItemIdentifierValue>
        </UniqueItemId>
    </ItemReceivedResponse>
</NCIPMessage> 

ITEMRECEIVED

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue, "ItemReceived -> Visible ID : " . $visid );
}

sub cancel_request_item {
    my $faidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:CancelRequestItem/ns1:InitiationHeader/ns1:FromAgencyId/ns1:AgencyId');
    my $taidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:CancelRequestItem/ns1:InitiationHeader/ns1:ToAgencyId/ns1:AgencyId');
    my $barcode = $doc->findvalue('/ns1:NCIPMessage/ns1:CancelRequestItem/ns1:ItemId/ns1:ItemIdentifierValue');
    my $pid  = $doc->findvalue('/ns1:NCIPMessage/ns1:CancelRequestItem/ns1:UserId/ns1:UserIdentifierValue');
    my $requestID  = $doc->findvalue('/ns1:NCIPMessage/ns1:CancelRequestItem/ns1:RequestId/ns1:RequestIdentifierValue');
 
    my $r = cancel_hold( $pid, $barcode );

    my $hd = <<ITEMREQUESTCANCELLED;
Content-type: text/xml

<?xml version="1.0" encoding="UTF-8"?><ns1:NCIPMessage ns1:version="http://www.niso.org/schemas/ncip/v2_0/imp1/xsd/ncip_v2_0.xsd" xmlns:ns1="http://www.niso.org/2008/ncip">
  <ns1:CancelRequestItemResponse>
    <ns1:RequestId>
      <ns1:RequestIdentifierValue>$requestID</ns1:RequestIdentifierValue>
    </ns1:RequestId>
    <ns1:UserId>
      <ns1:UserIdentifierValue>$pid</ns1:UserIdentifierValue>
    </ns1:UserId>
  </ns1:CancelRequestItemResponse>
</ns1:NCIPMessage>

ITEMREQUESTCANCELLED

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
        "CancelRequestItem -> Barcode : " . $barcode );
}

sub item_cancelled {
    my $faidSchemeX = $doc->findvalue('/NCIPMessage/ItemRequestCancelled/InitiationHeader/FromAgencyId/UniqueAgencyId/Scheme');
    my $faidScheme = HTML::Entities::encode($faidSchemeX);
    my $faidValue  = $doc->find('/NCIPMessage/ItemRequestCancelled/InitiationHeader/FromAgencyId/UniqueAgencyId/Value');

    my $taidSchemeX = $doc->findvalue('/NCIPMessage/ItemRequestCancelled/InitiationHeader/ToAgencyId/UniqueAgencyId/Scheme');
    my $taidScheme = HTML::Entities::encode($taidSchemeX);
    my $taidValue  = $doc->find('/NCIPMessage/ItemRequestCancelled/InitiationHeader/ToAgencyId/UniqueAgencyId/Value');
    my $UniqueItemIdAgencyIdValue = $doc->findvalue('/NCIPMessage/ItemRequestCancelled/UniqueItemId/UniqueAgencyId/Value');

    my $barcode = $doc->findvalue('/NCIPMessage/ItemRequestCancelled/UniqueItemId/ItemIdentifierValue');

    if ( $barcode =~ /^i/ ) {    # delete copy only if barcode is an iNUMBER
        $barcode .= $faidValue;
        my $copy = copy_from_barcode($barcode);
        fail( $copy->{textcode} . " $barcode" ) unless ( blessed $copy);
        my $r = delete_copy($copy);
    } else {

        # remove hold!
        my $copy = copy_from_barcode($barcode);
        fail( $copy->{textcode} . " $barcode" ) unless ( blessed $copy);
        my $r = update_copy( $copy, 0 ); # TODO: we need to actually remove the hold, not just reset to available
    }

    my $hd = <<ITEMREQUESTCANCELLED;
Content-type: text/xml


<!DOCTYPE NCIPMessage PUBLIC "-//NISO//NCIP DTD Version 1.0//EN" "http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
<NCIPMessage version="http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
    <ItemRequestCancelledResponse>
        <ResponseHeader>
            <FromAgencyId>
                <UniqueAgencyId>
                    <Scheme>$faidScheme</Scheme>
                    <Value>$faidValue</Value>
                </UniqueAgencyId>
            </FromAgencyId>
            <ToAgencyId>
                <UniqueAgencyId>
                    <Scheme>$taidScheme</Scheme>
                    <Value>$taidValue</Value>
                </UniqueAgencyId>
            </ToAgencyId>
        </ResponseHeader>
        <UniqueItemId>
            <ItemIdentifierValue datatype="string">$barcode</ItemIdentifierValue>
        </UniqueItemId>
    </ItemRequestCancelledResponse>
</NCIPMessage> 

ITEMREQUESTCANCELLED

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
        "ItemRequestCancelled -> Barcode : " . $barcode );
}

sub item_checked_in {
    my $faidSchemeX = $doc->findvalue('/NCIPMessage/ItemCheckedIn/InitiationHeader/FromAgencyId/UniqueAgencyId/Scheme');
    my $faidScheme = HTML::Entities::encode($faidSchemeX);
    my $faidValue  = $doc->find('/NCIPMessage/ItemCheckedIn/InitiationHeader/FromAgencyId/UniqueAgencyId/Value');
    my $taidSchemeX = $doc->findvalue('/NCIPMessage/ItemCheckedIn/InitiationHeader/ToAgencyId/UniqueAgencyId/Scheme');
    my $taidScheme = HTML::Entities::encode($taidSchemeX);
    my $taidValue  = $doc->find('/NCIPMessage/ItemCheckedIn/InitiationHeader/ToAgencyId/UniqueAgencyId/Value');

    my $visid = $doc->findvalue('/NCIPMessage/ItemCheckedIn/ItemOptionalFields/ItemDescription/VisibleItemId/VisibleItemIdentifier') . $faidValue;
    my $r = checkin($visid);
    my $copy = copy_from_barcode($visid);
    fail( $copy->{textcode} . " $visid" ) unless ( blessed $copy);
    my $r2 = update_copy( $copy, 113 ); # XXX CUSTOMIZATION NEEDED XXX # "INN-Reach Transit Return" status

    my $hd = <<ITEMCHECKEDIN;
Content-type: text/xml


<!DOCTYPE NCIPMessage PUBLIC "-//NISO//NCIP DTD Version 1.0//EN" "http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
<NCIPMessage version="http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
    <ItemCheckedInResponse>
        <ResponseHeader>
            <FromAgencyId>
                <UniqueAgencyId>
                    <Scheme>$faidScheme</Scheme>
                    <Value>$faidValue</Value>
                </UniqueAgencyId>
            </FromAgencyId>
            <ToAgencyId>
                <UniqueAgencyId>
                    <Scheme>$taidScheme</Scheme>
                    <Value>$taidValue</Value>
                </UniqueAgencyId>
            </ToAgencyId>
        </ResponseHeader>
        <UniqueItemId>
            <ItemIdentifierValue datatype="string">$visid</ItemIdentifierValue>
        </UniqueItemId>
    </ItemCheckedInResponse>
</NCIPMessage> 

ITEMCHECKEDIN

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue, "ItemCheckedIn -> Visible ID : " . $visid );
}

sub item_checked_out {
    my $faidSchemeX = $doc->findvalue('/NCIPMessage/ItemCheckedOut/InitiationHeader/FromAgencyId/UniqueAgencyId/Scheme');
    my $faidScheme = HTML::Entities::encode($faidSchemeX);
    my $faidValue  = $doc->find('/NCIPMessage/ItemCheckedOut/InitiationHeader/FromAgencyId/UniqueAgencyId/Value');
    my $taidSchemeX = $doc->findvalue('/NCIPMessage/ItemCheckedOut/InitiationHeader/ToAgencyId/UniqueAgencyId/Scheme');
    my $taidScheme = HTML::Entities::encode($taidSchemeX);
    my $taidValue  = $doc->find('/NCIPMessage/ItemCheckedOut/InitiationHeader/ToAgencyId/UniqueAgencyId/Value');

    my $patron_barcode = $doc->findvalue('/NCIPMessage/ItemCheckedOut/UserOptionalFields/VisibleUserId/VisibleUserIdentifier');
    my $due_date = $doc->findvalue('/NCIPMessage/ItemCheckedOut/DateDue');
    my $visid = $doc->findvalue('/NCIPMessage/ItemCheckedOut/ItemOptionalFields/ItemDescription/VisibleItemId/VisibleItemIdentifier') . $faidValue;

    my $copy = copy_from_barcode($visid);
    fail( $copy->{textcode} . " $visid" ) unless ( blessed $copy);
    my $r = update_copy( $copy, 0 ); # seemed like copy had to be available before it could be checked out, so ...
    my $r1 = checkin($visid) if ( $copy->status == OILS_COPY_STATUS_CHECKED_OUT ); # double posted itemcheckedout messages cause error ... trying to simplify
    my $r2 = checkout( $visid, $patron_barcode, $due_date );

    my $hd = <<ITEMCHECKEDOUT;
Content-type: text/xml


<!DOCTYPE NCIPMessage PUBLIC "-//NISO//NCIP DTD Version 1.0//EN" "http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
<NCIPMessage version="http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
    <ItemCheckedOutResponse>
        <ResponseHeader>
            <FromAgencyId>
                <UniqueAgencyId>
                    <Scheme>$faidScheme</Scheme>
                    <Value>$faidValue</Value>
                </UniqueAgencyId>
            </FromAgencyId>
            <ToAgencyId>
                <UniqueAgencyId>
                    <Scheme>$taidScheme</Scheme>
                    <Value>$taidValue</Value>
                </UniqueAgencyId>
            </ToAgencyId>
        </ResponseHeader>
        <UniqueItemId>
            <ItemIdentifierValue datatype="string">$visid</ItemIdentifierValue>
        </UniqueItemId>
    </ItemCheckedOutResponse>
</NCIPMessage> 

ITEMCHECKEDOUT

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
        "ItemCheckedOut -> Visible Id : " . $visid . " | Patron Barcode : " . $patron_barcode . " | Due Date : " . $due_date );
}

sub check_out_item {
    my $faidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckOutItem/ns1:InitiationHeader/ns1:FromAgencyId/ns1:AgencyId');
    my $taidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckOutItem/ns1:InitiationHeader/ns1:ToAgencyId/ns1:AgencyId');

    my $patron_barcode  = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckOutItem/ns1:UserId/ns1:UserIdentifierValue');

    my $aidValue = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckOutItem/ns1:ItemId/ns1:AgencyId');
    my $barcode = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckOutItem/ns1:ItemId/ns1:ItemIdentifierValue');

    my $due_date = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckOutItem/ns1:DesiredDateDue');

    my $copy = copy_from_barcode($barcode);
    fail( $copy->{textcode} . " $barcode" ) unless ( blessed $copy);

    $due_date = checkout( $barcode, $patron_barcode, $due_date );
    $due_date = substr($due_date, 0, 10)."T23:59:59Z"; 

    my $hd = <<CHECKOUTITEM;
Content-type: text/xml


<ns1:NCIPMessage ns1:version="http://www.niso.org/ncip/v2_0/imp1/xsd/ncip_v2_0.xsd" xmlns:ns1="http://www.niso.org/2008/ncip" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:schemaLocation="http://www.niso.org/2008/ncip ncip_v2_0.xsd">
  <ns1:CheckOutItemResponse>
     <ns1:ItemId>
        <ns1:AgencyId ns1:Scheme="localhost/ncip/v1/schemes/agencies/1">$aidValue</ns1:AgencyId>
        <ns1:ItemIdentifierValue>$barcode</ns1:ItemIdentifierValue>
     </ns1:ItemId>
     <ns1:UserId>
        <ns1:AgencyId ns1:Scheme="localhost/ncip/v1/schemes/agencies/1">MIT</ns1:AgencyId>
        <ns1:UserIdentifierValue>$patron_barcode</ns1:UserIdentifierValue>
     </ns1:UserId>
     <ns1:DateDue>$due_date</ns1:DateDue>
  </ns1:CheckOutItemResponse>
</ns1:NCIPMessage>


CHECKOUTITEM

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
        "CheckOutItem -> Barcode : " . $barcode . " | Patron Barcode : " . $patron_barcode . " | Due Date : " . $due_date );
}

sub check_in_item {
    my $faidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckInItem/ns1:InitiationHeader/ns1:FromAgencyId/ns1:AgencyId');
    my $taidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckInItem/ns1:InitiationHeader/ns1:ToAgencyId/ns1:AgencyId');
    my $aidValue = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckInItem/ns1:ItemId/ns1:AgencyId');
    my $barcode = $doc->findvalue('/ns1:NCIPMessage/ns1:CheckInItem/ns1:ItemId/ns1:ItemIdentifierValue');
    my $r = checkin($barcode);
    fail($r) if $r =~ /^COPY_NOT_CHECKED_OUT/;
    my $copy = copy_from_barcode($barcode);
    fail($copy->{textcode}." $barcode") unless (blessed $copy);
    my $r2 = update_copy($copy,6); # In-transit status 

    my $hd = <<CHECKINITEM;
Content-type: text/xml


<ns1:NCIPMessage ns1:version="http://www.niso.org/ncip/v2_0/imp1/xsd/ncip_v2_0.xsd" xmlns:ns1="http://www.niso.org/2008/ncip" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:schemaLocation="http://www.niso.org/2008/ncip ncip_v2_0.xsd">
  <ns1:CheckInItemResponse>
     <ns1:ItemId>
        <ns1:AgencyId ns1:Scheme="localhost/ncip/v1/schemes/agencies/1">$aidValue</ns1:AgencyId>
        <ns1:ItemIdentifierValue>$barcode</ns1:ItemIdentifierValue>
     </ns1:ItemId>
  </ns1:CheckInItemResponse>
</ns1:NCIPMessage>

CHECKINITEM

    logit( $hd, ( caller(0) )[3] );
    # staff_log( $taidValue, $faidValue, "CheckInItem -> Barcode : " . $barcode );
    staff_log( $taidValue, $faidValue, "CheckInItem -> Barcode : " . $barcode );
}

sub item_shipped {
    my $faidSchemeX = $doc->findvalue('/NCIPMessage/ItemShipped/InitiationHeader/FromAgencyId/UniqueAgencyId/Scheme');
    my $faidScheme = HTML::Entities::encode($faidSchemeX);
    my $faidValue  = $doc->find('/NCIPMessage/ItemShipped/InitiationHeader/FromAgencyId/UniqueAgencyId/Value');
    my $taidSchemeX = $doc->findvalue('/NCIPMessage/ItemShipped/InitiationHeader/ToAgencyId/UniqueAgencyId/Scheme');
    my $taidScheme = HTML::Entities::encode($taidSchemeX);
    my $taidValue  = $doc->find('/NCIPMessage/ItemShipped/InitiationHeader/ToAgencyId/UniqueAgencyId/Value');

    my $visid = $doc->findvalue('/NCIPMessage/ItemShipped/ItemOptionalFields/ItemDescription/VisibleItemId/VisibleItemIdentifier') . $faidValue;
    my $barcode = $doc->findvalue('/NCIPMessage/ItemShipped/UniqueItemId/ItemIdentifierValue') . $faidValue;
    my $title = $doc->findvalue('/NCIPMessage/ItemShipped/ItemOptionalFields/BibliographicDescription/Title');
    my $callnumber = $doc->findvalue('/NCIPMessage/ItemShipped/ItemOptionalFields/ItemDescription/CallNumber');

    my $copy = copy_from_barcode($barcode);
    fail( $copy->{textcode} . " $barcode" ) unless ( blessed $copy);
    my $r = update_copy_shipped( $copy, 112, $visid );    # XXX CUSTOMIZATION NEEDED XXX # put copy into INN-Reach Transit status & modify barcode = Visid != tempIIIiNumber

    my $hd = <<ITEMSHIPPED;
Content-type: text/xml


<!DOCTYPE NCIPMessage PUBLIC "-//NISO//NCIP DTD Version 1.0//EN" "http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
<NCIPMessage version="http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
    <ItemShippedResponse>
        <ResponseHeader>
            <FromAgencyId>
                <UniqueAgencyId>
                    <Scheme>$faidScheme</Scheme>
                    <Value>$faidValue</Value>
                </UniqueAgencyId>
            </FromAgencyId>
            <ToAgencyId>
                <UniqueAgencyId>
                    <Scheme>$taidScheme</Scheme>
                    <Value>$taidValue</Value>
                </UniqueAgencyId>
            </ToAgencyId>
        </ResponseHeader>
        <UniqueItemId>
            <ItemIdentifierValue datatype="string">$visid</ItemIdentifierValue>
        </UniqueItemId>
    </ItemShippedResponse>
</NCIPMessage> 

ITEMSHIPPED

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
        "ItemShipped -> Visible Id : " . $visid . " | Barcode : " . $barcode . " | Title : " . $title . " | Call Number : " . $callnumber );
}

sub request_item {
    my $faidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:RequestItem/ns1:InitiationHeader/ns1:FromAgencyId/ns1:AgencyId');
    my $taidValue  = $doc->findvalue('/ns1:NCIPMessage/ns1:RequestItem/ns1:InitiationHeader/ns1:ToAgencyId/ns1:AgencyId');

    my $pid = $doc->findvalue('/ns1:NCIPMessage/ns1:RequestItem/ns1:UserId/ns1:UserIdentifierValue');
    my $bid = $doc->findvalue('/ns1:NCIPMessage/ns1:RequestItem/ns1:BibliographicId/ns1:BibliographicRecordId/ns1:BibliographicRecordIdentifier');

    my $request_id = $doc->findvalue('/ns1:NCIPMessage/ns1:RequestItem/ns1:RequestId/ns1:RequestIdentifierValue');
    my $request_type = $doc->findvalue('/ns1:NCIPMessage/ns1:RequestItem/ns1:RequestType');
    my $request_scope_type = $doc->findvalue('/ns1:NCIPMessage/ns1:RequestItem/ns1:RequestScopeType');
  
    my $r = "default error checking response";

    my $copy_status_id = 101;    # XXX CUSTOMIZATION NEEDED XXX # INN-Reach Loan Requested - local configured status
	
    # check if having any copy available
    my $copy = copy_from_bid($bid);
    fail( $copy->{textcode} . " $visid" ) unless ( blessed $copy);

    my $item_id   = place_hold('T', $bid, $pid, $taidValue);

    my $hd = <<ITEMREQ;
Content-type: text/xml

<ns1:NCIPMessage ns1:version="http://www.niso.org/schemas/ncip/v2_0/imp1/xsd/ncip_v2_0.xsd" xmlns:ns1="http://www.niso.org/2008/ncip">
    <ns1:RequestItemResponse>
        <ns1:RequestId>
            <ns1:RequestIdentifierValue>$request_id</ns1:RequestIdentifierValue>
        </ns1:RequestId>
        <ns1:ItemId>
            <ns1:ItemIdentifierValue>$item_id</ns1:ItemIdentifierValue>
        </ns1:ItemId>
        <ns1:UserId>
            <ns1:UserIdentifierValue>$pid</ns1:UserIdentifierValue>
        </ns1:UserId>
        <ns1:RequestType ns1:Scheme="http://www.niso.org/ncip/v1_0/imp1/schemes/requesttype/requesttype.scm">$request_type</ns1:RequestType>
        <ns1:RequestScopeType ns1:Scheme="http://www.niso.org/ncip/v1_0/imp1/schemes/requestscopetype/requestscopetype.scm">$request_scope_type</ns1:RequestScopeType>
    </ns1:RequestItemResponse>
</ns1:NCIPMessage>

ITEMREQ

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
        "Requeste_Item -> Bib ID : " . $bid . " | Patronid :" . $pid );
}

sub item_request {
    my $faidSchemeX = $doc->findvalue('/NCIPMessage/ItemRequested/InitiationHeader/FromAgencyId/UniqueAgencyId/Scheme');
    my $faidScheme = HTML::Entities::encode($faidSchemeX);
    my $faidValue  = $doc->find('/NCIPMessage/ItemRequested/InitiationHeader/FromAgencyId/UniqueAgencyId/Value');

    my $taidSchemeX = $doc->findvalue('/NCIPMessage/ItemRequested/InitiationHeader/ToAgencyId/UniqueAgencyId/Scheme');
    my $taidScheme = HTML::Entities::encode($taidSchemeX);
    my $taidValue  = $doc->find('/NCIPMessage/ItemRequested/InitiationHeader/ToAgencyId/UniqueAgencyId/Value');
    my $UniqueItemIdAgencyIdValue = $doc->findvalue('/NCIPMessage/ItemRequested/UniqueItemId/UniqueAgencyId/Value');

    # TODO: should we use the VisibleID for item agency variation of this method call

    my $pid = $doc->findvalue('/NCIPMessage/ItemRequested/UniqueUserId/UserIdentifierValue');
    my $barcode = $doc->findvalue('/NCIPMessage/ItemRequested/UniqueItemId/ItemIdentifierValue');
    my $author = $doc->findvalue('/NCIPMessage/ItemRequested/ItemOptionalFields/BibliographicDescription/Author');
    my $title = $doc->findvalue('/NCIPMessage/ItemRequested/ItemOptionalFields/BibliographicDescription/Title');
    my $callnumber = $doc->findvalue('/NCIPMessage/ItemRequested/ItemOptionalFields/ItemDescription/CallNumber');
    my $medium_type = $doc->find('/NCIPMessage/ItemRequested/ItemOptionalFields/BibliographicDescription/MediumType/Value');

    my $r = "default error checking response";

    if ( $barcode =~ /^i/ ) {    # XXX EG is User Agency # create copy only if barcode is an iNUMBER
        my $copy_status_id = 110;    # XXX CUSTOMIZATION NEEDED XXX # INN-Reach Loan Requested - local configured status
        $barcode .= $faidValue;
        # we want our custom status to be then end result, so create the copy with status of "Available, then hold it, then update the status
        $r = create_copy( $title, $callnumber, $barcode, 0, $medium_type );
        my $copy = copy_from_barcode($barcode);
        my $r2   = place_simple_hold( $copy->id, $pid );
        my $r3   = update_copy( $copy, $copy_status_id );
    } else {    # XXX EG is Item Agency
        # place hold for user UniqueUserId/UniqueAgencyId/Value = institution account
        my $copy = copy_from_barcode($barcode);
        my $pid2 = 1013459; # XXX CUSTOMIZATION NEEDED XXX # this is the id of a user representing your DCB system, TODO: use agency information to create and link to individual accounts per agency, if needed
        $r = place_simple_hold( $copy->id, $pid2 );
        my $r2 = update_copy( $copy, 111 ); # XXX CUSTOMIZATION NEEDED XXX # put into INN-Reach Hold status
    }

    my $hd = <<ITEMREQ;
Content-type: text/xml


<!DOCTYPE NCIPMessage PUBLIC "-//NISO//NCIP DTD Version 1.0//EN" "http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
<NCIPMessage version="http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
    <ItemRequestedResponse>
        <ResponseHeader>
            <FromAgencyId>
                <UniqueAgencyId>
                    <Scheme>$faidScheme</Scheme>
                    <Value>$faidValue</Value>
                </UniqueAgencyId>
            </FromAgencyId>
            <ToAgencyId>
                <UniqueAgencyId>
                    <Scheme>$taidScheme</Scheme>
                    <Value>$taidValue</Value>
                </UniqueAgencyId>
            </ToAgencyId>
        </ResponseHeader>
        <UniqueUserId>
            <UniqueAgencyId>
                <Scheme datatype="string">$taidScheme</Scheme>
                <Value datatype="string">$taidValue</Value>
            </UniqueAgencyId>
            <UserIdentifierValue datatype="string">$pid</UserIdentifierValue>
        </UniqueUserId>
        <UniqueItemId>
            <ItemIdentifierValue datatype="string">$barcode</ItemIdentifierValue>
        </UniqueItemId>
        <ItemOptionalFields>
            <BibliographicDescription>
        <Author datatype="string">$author</Author>
        <Title datatype="string">$title</Title>
            </BibliographicDescription>
            <ItemDescription>
                <CallNumber datatype="string">$callnumber</CallNumber>
            </ItemDescription>
       </ItemOptionalFields>
    </ItemRequestedResponse>
</NCIPMessage> 

ITEMREQ

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
        "ItemRequested -> Barcode : " . $barcode . " | Title : " . $title . " | Call Number : " . $callnumber . " | Patronid :" . $pid );
}

sub lookupUser {

    my $faidValue = $doc->find('/ns1:NCIPMessage/ns1:LookupUser/ns1:UserID/ns1:AgencyId');
    my $id = $doc->findvalue('/ns1:NCIPMessage/ns1:LookupUser/ns1:UserId/ns1:UserIdentifierValue');
    my $uidValue = user_id_from_barcode($id);

    if ( !defined($uidValue)
        || ( ref($uidValue) && reftype($uidValue) eq 'HASH' ) )
    {
        do_lookup_user_error_stanza("PATRON_NOT_FOUND : $id");
        die;
    }

    my ( $propername, $email, $good_until, $userprivid, $block_stanza ) =
      ( "name here", "", "good until", "0", "" );    # defaults

    my $patron = flesh_user($uidValue);

    #if (blessed($patron)) {
    my $patron_ok = 1;
    my @penalties = @{ $patron->standing_penalties };

    if ( $patron->deleted eq 't' ) {
        do_lookup_user_error_stanza("PATRON_DELETED : $uidValue");
        die;
    } elsif ( $patron->barred eq 't' ) {
        do_lookup_user_error_stanza("PATRON_BARRED : $uidValue");
        die;
    } elsif ( $patron->active eq 'f' ) {
        do_lookup_user_error_stanza("PATRON_INACTIVE : $uidValue");
        die;
    }

    elsif ( $#penalties > -1 ) {

#                my $penalty;
#                   foreach $penalty (@penalties) {
#                    if (defined($penalty->standing_penalty->block_list)) {
#                            my @block_list = split(/\|/, $penalty->standing_penalty->block_list);
#                            foreach my $block (@block_list) {
#                                foreach my $block_on (@$block_types) {
#                                    if ($block eq $block_on) {
#                                        $block_stanza .= "\n".$penalty->standing_penalty->name;
#                                        $patron_ok = 0;
#                                    }
#                                    last unless ($patron_ok);
#                            }
#                                last unless ($patron_ok);
#                          }
#                     }
#                }
        $block_stanza = qq(
            <BlockOrTrap>
                <UniqueAgencyId>
                    <Scheme datatype="string">http://just.testing.now</Scheme>
                    <Value datatype="string">$faidValue</Value>
                </UniqueAgencyId>
                <BlockOrTrapType>
                    <Scheme datatype="string">http://just.testing.now</Scheme>
                    <Value datatype="string">Block Hold</Value>
                </BlockOrTrapType>
            </BlockOrTrap>);
    }

    if ( defined( $patron->email ) ) {
        $email = qq(
            <UserAddressInformation>
                <ElectronicAddress>
                    <ElectronicAddressType>
                        <Scheme datatype="string">http://testing.now</Scheme>
                        <Value datatype="string">mailto</Value>
                    </ElectronicAddressType>
                    <ElectronicAddressData datatype="string">)
          . HTML::Entities::encode( $patron->email )
          . qq(</ElectronicAddressData>
                </ElectronicAddress>
            </UserAddressInformation>);
    }

    $propername = $patron->first_given_name . " " . $patron->family_name;
    $good_until = $patron->expire_date || "unknown";
    $userprivid = $patron->profile;
    my $userou   = $patron->home_ou->name;
    my $userpriv = $patron->profile->name;

    #} else {
    #    do_lookup_user_error_stanza("PATRON_NOT_FOUND : $id");
    #    die;
    #}
    my $uniqid = $patron->id;
    my $visid  = $patron->card->barcode;
    my $hd = <<LOOKUPUSERRESPONSE;
Content-type: text/xml


<ns1:NCIPMessage xmlns:ns1="http://www.niso.org/2008/ncip" ns1:version="http://www.niso.org/schemas/ncip/v2_0/imp1/xsd/ncip_v2_0.xsd">
  <ns1:LookupUserResponse>
     <ns1:UserId>
        <ns1:AgencyId>$faidValue</ns1:AgencyId>
        <ns1:UserIdentifierValue>$id</ns1:UserIdentifierValue>
     </ns1:UserId>
     <ns1:UserOptionalFields>
        <ns1:NameInformation>
           <ns1:PersonalNameInformation>
              <ns1:UnstructuredPersonalUserName>Doe, John</ns1:UnstructuredPersonalUserName>
           </ns1:PersonalNameInformation>
        </ns1:NameInformation>
        <ns1:UserAddressInformation>
           <ns1:UserAddressRoleType>Primary Address</ns1:UserAddressRoleType>
           <ns1:PhysicalAddress>
              <ns1:StructuredAddress>
                 <ns1:Line1>1 Main Street</ns1:Line1>
                 <ns1:Locality>Northampton</ns1:Locality>
                 <ns1:Region> PA</ns1:Region>
                 <ns1:PostalCode>18067-1003</ns1:PostalCode>
              </ns1:StructuredAddress>
              <ns1:PhysicalAddressType>Postal Address</ns1:PhysicalAddressType>
           </ns1:PhysicalAddress>
        </ns1:UserAddressInformation>
        <ns1:UserAddressInformation>
           <ns1:UserAddressRoleType>Home</ns1:UserAddressRoleType>
           <ns1:ElectronicAddress>
              <ns1:ElectronicAddressType>mailto</ns1:ElectronicAddressType>
              <ns1:ElectronicAddressData></ns1:ElectronicAddressData>
           </ns1:ElectronicAddress>
        </ns1:UserAddressInformation>
        <ns1:UserLanguage>ENGLISH</ns1:UserLanguage>
        <ns1:UserPrivilege>
           <ns1:AgencyId>LEHI</ns1:AgencyId>
           <ns1:AgencyUserPrivilegeType>LIBRARY</ns1:AgencyUserPrivilegeType>
           <ns1:UserPrivilegeStatus>
              <ns1:UserPrivilegeStatusType>LEHIGH</ns1:UserPrivilegeStatusType>
           </ns1:UserPrivilegeStatus>
           <ns1:UserPrivilegeDescription>User Library</ns1:UserPrivilegeDescription>
        </ns1:UserPrivilege>
        <ns1:UserPrivilege>
           <ns1:AgencyId>LEHI</ns1:AgencyId>
           <ns1:AgencyUserPrivilegeType>PROFILE</ns1:AgencyUserPrivilegeType>
           <ns1:UserPrivilegeStatus>
              <ns1:UserPrivilegeStatusType>FACULTY</ns1:UserPrivilegeStatusType>
           </ns1:UserPrivilegeStatus>
           <ns1:UserPrivilegeDescription>User Profile</ns1:UserPrivilegeDescription>
        </ns1:UserPrivilege>
        <ns1:UserPrivilege>
           <ns1:AgencyId>LEHI</ns1:AgencyId>
           <ns1:AgencyUserPrivilegeType>STATUS</ns1:AgencyUserPrivilegeType>
           <ns1:UserPrivilegeStatus>
              <ns1:UserPrivilegeStatusType>OK</ns1:UserPrivilegeStatusType>
           </ns1:UserPrivilegeStatus>
           <ns1:UserPrivilegeDescription>User Status</ns1:UserPrivilegeDescription>
        </ns1:UserPrivilege>
        <ns1:UserPrivilege>
           <ns1:AgencyId>LEHI</ns1:AgencyId>
           <ns1:AgencyUserPrivilegeType>CAT1</ns1:AgencyUserPrivilegeType>
           <ns1:UserPrivilegeStatus>
              <ns1:UserPrivilegeStatusType>LIBRARY AN</ns1:UserPrivilegeStatusType>
           </ns1:UserPrivilegeStatus>
           <ns1:UserPrivilegeDescription>User Category One</ns1:UserPrivilegeDescription>
        </ns1:UserPrivilege>
     </ns1:UserOptionalFields>
  </ns1:LookupUserResponse>
</ns1:NCIPMessage>

LOOKUPUSERRESPONSE

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue,
            "LookupUser -> Patron Barcode : "
          . $id
          . " | Patron Id : "
          . $uidValue
          . " | User Name : "
          . $propername
          . " | User Priv : "
          . $userpriv );
}

sub fail {
    my $error_msg =
      shift || "THIS IS THE DEFAULT / DO NOT HANG III NCIP RESP MSG";
    print "Content-type: text/xml\n\n";

    print <<ITEMREQ;

<ns1:NCIPMessage ns1:version="http://www.niso.org/ncip/v2_0/imp1/xsd/ncip_v2_0.xsd" xmlns:ns1="http://www.niso.org/2008/ncip" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:schemaLocation="http://www.niso.org/2008/ncip ncip_v2_0.xsd">
   <ns1:Problem>
     <ns1:ProblemType ns1:Scheme="http://www.niso.org/ncip/v1_0/schemes/messagingerrortype/messagingerrortype.scm">Unknown/Error Service</ns1:ProblemType>
     <ns1:ProblemElement>$error_msg</ns1:ProblemElement>
   </ns1:Problem>
</ns1:NCIPMessage>

ITEMREQ

    staff_log( $taidValue, $faidValue,
        ( ( caller(0) )[3] . " -> " . $error_msg ) );
    die;
}

sub do_lookup_user_error_stanza {

    my $error = shift;
    my $hd    = <<LOOKUPPROB;
Content-type: text/xml


<!DOCTYPE NCIPMessage PUBLIC "-//NISO//NCIP DTD Version 1.0//EN" "http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
<NCIPMessage version="http://www.niso.org/ncip/v1_0/imp1/dtd/ncip_v1_0.dtd">
    <LookupUserResponse>
        <ResponseHeader>
            <FromAgencyId>
                <UniqueAgencyId>
                    <Scheme>$taidScheme</Scheme>
                    <Value>$taidValue</Value>
                </UniqueAgencyId>
            </FromAgencyId>
            <ToAgencyId>
                <UniqueAgencyId>
                    <Scheme>$faidScheme</Scheme>
                    <Value>$faidValue</Value>
                </UniqueAgencyId>
            </ToAgencyId>
        </ResponseHeader>
        <Problem>
            <ProcessingError>
                <ProcessingErrorType>
                    <Scheme>http://www.niso.org/ncip/v1_0/schemes/processingerrortype/lookupuserprocessingerror.scm</Scheme>
                    <Value>$error</Value>
                </ProcessingErrorType>
                <ProcessingErrorElement>
                    <ElementName>AuthenticationInput</ElementName>
                </ProcessingErrorElement>
            </ProcessingError>
        </Problem>
    </LookupUserResponse>
</NCIPMessage>

LOOKUPPROB

    logit( $hd, ( caller(0) )[3] );
    staff_log( $taidValue, $faidValue, ( ( caller(0) )[3] . " -> " . $error ) );
    die;
}

# Login to the OpenSRF system/Evergreen.
#
# Returns a hash with the authtoken, authtime, and expiration (time in
# seconds since 1/1/1970).
sub login {

 # XXX: local opensrf core conf filename should be in config.
 # XXX: STAFF account with ncip service related permissions should be in config.
    my $bootstrap = '/openils/conf/opensrf_core.xml';
    my $uname     = "ursername_here";    
    my $password  = "password_here";   

    # Bootstrap the client
    OpenSRF::System->bootstrap_client( config_file => $bootstrap );
    my $idl = OpenSRF::Utils::SettingsClient->new->config_value("IDL");
    Fieldmapper->import( IDL => $idl );

    # Initialize CStoreEditor:
    OpenILS::Utils::CStoreEditor->init;

    my $seed = OpenSRF::AppSession->create('open-ils.auth')
      ->request( 'open-ils.auth.authenticate.init', $uname )->gather(1);

    return undef unless $seed;

    my $response = OpenSRF::AppSession->create('open-ils.auth')->request(
        'open-ils.auth.authenticate.complete',
        {
            username => $uname,
            password => md5_hex( $seed . md5_hex($password) ),
            type     => 'staff'
        }
    )->gather(1);

    return undef unless $response;

    my %result;
    $result{'authtoken'}  = $response->{payload}->{authtoken};
    $result{'authtime'}   = $response->{payload}->{authtime};
    $result{'expiration'} = time() + $result{'authtime'}
      if ( defined( $result{'authtime'} ) );
    return %result;
}

# Check the time versus the session expiration time and login again if
# the session has expired, consequently resetting the session
# paramters. We want to run this before doing anything that requires
# us to have a current session in OpenSRF.
#
# Arguments
# none
#
# Returns
# Nothing
sub check_session_time {
    if ( time() > $session{'expiration'} ) {
        %session = login();
        if ( !%session ) {
            die("Failed to reinitialize the session after expiration.");
        }
    }
}

# Retrieve the logged in user.
#
sub get_session {
    my $response =
      OpenSRF::AppSession->create('open-ils.auth')
      ->request( 'open-ils.auth.session.retrieve', $session{authtoken} )
      ->gather(1);
    return $response;
}

# Logout/destroy the OpenSRF session
#
# Argument is
# none
#
# Returns
# Does not return anything
sub logout {
    if ( time() < $session{'expiration'} ) {
        my $response =
          OpenSRF::AppSession->create('open-ils.auth')
          ->request( 'open-ils.auth.session.delete', $session{authtoken} )
          ->gather(1);
        if ($response) {

            # strong.silent.success
            exit(0);
        } else {
            fail("Logout unsuccessful. Good-bye, anyway.");
        }
    }
}

sub update_copy {
    check_session_time();
    my ( $copy, $status_id ) = @_;
    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );
    $e->xact_begin;
    $copy->status($status_id);
    return $e->event unless $e->update_asset_copy($copy);
    $e->commit;
    return 'SUCCESS';
}

# my paranoia re barcode on shipped items using visid for unique value
sub update_copy_shipped {
    check_session_time();
    my ( $copy, $status_id, $barcode ) = @_;
    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );
    $e->xact_begin;
    $copy->status($status_id);
    $copy->barcode($barcode);
    return $e->event unless $e->update_asset_copy($copy);
    $e->commit;
    return 'SUCCESS';
}

# Delete a copy
#
# Argument
# Fieldmapper asset.copy object
#
# Returns
# "SUCCESS" on success
# Event textcode if an error occurs
sub delete_copy {
    check_session_time();
    my ($copy) = @_;

    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );

    # Get the calnumber
    my $vol = $e->retrieve_asset_call_number( $copy->call_number );
    return $e->event->{textcode} unless ($vol);

    # Get the biblio.record_entry
    my $bre = $e->retrieve_biblio_record_entry( $vol->record );
    return $e->event->{textcode} unless ($bre);

    # Delete everything in a transaction and rollback if anything fails.
    # TODO: I think there is a utility function which handles all this
    $e->xact_begin;
    my $r;    # To hold results of editor calls
    $r = $e->delete_asset_copy($copy);
    unless ($r) {
        my $lval = $e->event->{textcode};
        $e->rollback;
        return $lval;
    }
    my $list =
      $e->search_asset_copy( { call_number => $vol->id, deleted => 'f' } );
    unless (@$list) {
        $r = $e->delete_asset_call_number($vol);
        unless ($r) {
            my $lval = $e->event->{textcode};
            $e->rollback;
            return $lval;
        }
        $list = $e->search_asset_call_number( { record => $bre->id, deleted => 'f' } );
        unless (@$list) {
            $r = $e->delete_biblio_record_entry($bre);
            unless ($r) {
                my $lval = $e->event->{textcode};
                $e->rollback;
                return $lval;
            }
        }
    }
    $e->commit;
    return 'SUCCESS';
}

# Get asset.copy from asset.copy.barcode.
# Arguments
# copy barcode
#
# Returns
# asset.copy fieldmaper object
# or hash on error
sub copy_from_barcode {
    check_session_time();
    my ($barcode) = @_;
    my $response =
      OpenSRF::AppSession->create('open-ils.search')
      ->request( 'open-ils.search.asset.copy.find_by_barcode', $barcode )
      ->gather(1);
    return $response;
}

sub copy_from_bid {
    check_session_time();
    my ($bid) = @_;

    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );

    my $copy = $e->search_asset_copy(
    [
        {
            'deleted' => 'f',
            'holdable' => 't',
        },
        {
            'join' => {
                'acn' => {
                    'filter' => {'record' => $bid}
                }
            }
        }
    ]);
    
    # handle error if no item
    fail('Unknown Item - Bid: ' . $bid) unless (@$copy);

    # Check copy and holds status
    my $cpok;
    my $nocopy = 1;
    my $countavai = 0;
    my $countholdsnocp = 0;
    foreach my $cp (@$copy) {                  
      if ( ( $cp->status == OILS_COPY_STATUS_AVAILABLE ) or ( $cp->status == OILS_COPY_STATUS_RESHELVING ) ) {
        $cpok = $cp;
        $nocopy = 0;
        $countavai = $countavai + 1;
      }
    }

    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );

    my $holds = $e->search_action_hold_request(
       [ 
            {
                target => $bid,
                fulfillment_time => undef,
                cancel_time => undef,
                capture_time => undef,
                frozen => 0,
            },
            {
            'join' => {
                'ahtc' => {
                   'filter' => {'record' => $bid}
                }
            }
        }

       ]
    );

    if ( @$holds ){
      foreach my $h (@$holds) {
        $countholdsnocp = $countholdsnocp + 1;
      }
    }
    
    fail("Copy: ".$countavai." | Holds: ".$countholdsnocp);
    if ($countavai - $countholdsnocp <= 0) { fail('No copy available for Bid: ' . $bid);}

    return $cpok;
}

sub locid_from_barcode {
    my ($barcode) = @_;
    my $response =
      OpenSRF::AppSession->create('open-ils.search')
      ->request( 'open-ils.search.biblio.find_by_barcode', $barcode )
      ->gather(1);
    return $response->{ids}[0];
}

# Convert a MARC::Record to XML for Evergreen
#
# Copied from Dyrcona's issa framework which copied
# it from MVLC's Safari Load program which copied it
# from some code in the Open-ILS example import scripts.
#
# Argument
# A MARC::Record object
#
# Returns
# String with XML for the MARC::Record as Evergreen likes it
sub convert2marcxml {
    my $input = shift;
    ( my $xml = $input->as_xml_record() ) =~ s/\n//sog;
    $xml =~ s/^<\?xml.+\?\s*>//go;
    $xml =~ s/>\s+</></go;
    $xml =~ s/\p{Cc}//go;
    $xml = $U->entityize($xml);
    $xml =~ s/[\x00-\x1f]//go;
    return $xml;
}

# Create a copy and marc record
#
# Arguments
# title
# call number
# copy barcode
#
# Returns
# bib id on succes
# event textcode on failure
sub create_copy {
    check_session_time();
    my ( $title, $callnumber, $barcode, $copy_status_id, $medium_type ) = @_;


    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );

    my $r = $e->allowed( [ 'CREATE_COPY', 'CREATE_MARC', 'CREATE_VOLUME' ] );
    if ( ref($r) eq 'HASH' ) {
        return $r->{textcode} . ' ' . $r->{ilsperm};
    }

    # Check if the barcode exists in asset.copy and bail if it does.
    my $list = $e->search_asset_copy( { deleted => 'f', barcode => $barcode } );
    if (@$list) {
    # in the future, can we update it, if it exists and only if it is an INN-Reach status item ?
        $e->finish;
        fail( 'BARCODE_EXISTS ! Barcode : ' . $barcode );
        die;
    }

    # Create MARC record
    my $record = MARC::Record->new();
    $record->encoding('UTF-8');
    $record->leader('00881nam a2200193 4500');
    my $datespec = strftime( "%Y%m%d%H%M%S.0", localtime );
    my @fields = ();
    push( @fields, MARC::Field->new( '005', $datespec ) );
    push( @fields, MARC::Field->new( '082', '0', '4', 'a' => $callnumber ) );
    push( @fields, MARC::Field->new( '245', '0', '0', 'a' => $title ) );
    $record->append_fields(@fields);

    # Convert the record to XML
    my $xml = convert2marcxml($record);

    my $bre =
      OpenSRF::AppSession->create('open-ils.cat')
      ->request( 'open-ils.cat.biblio.record.xml.import',
        $session{authtoken}, $xml, 'System Local', 1 )->gather(1);
    return $bre->{textcode} if ( ref($bre) eq 'HASH' );

    # Create volume record
    my $vol =
      OpenSRF::AppSession->create('open-ils.cat')
      ->request( 'open-ils.cat.call_number.find_or_create', $session{authtoken}, $callnumber, $bre->id, 2 )   # XXX CUSTOMIZATION NEEDED XXX
      ->gather(1);
    return $vol->{textcode} if ( $vol->{textcode} );

    # Retrieve the user
    my $user = get_session;

    # Create copy record
    my $copy = Fieldmapper::asset::copy->new();
    # XXX CUSTOMIZATION NEEDED XXX
    # You will need to either create a circ mod for every expected medium type,
    # OR you should create a single circ mod for all requests from the external
    # system.
    # Adjust these lines as needed.
    #    $copy->circ_modifier(qq($medium_type)); # XXX CUSTOMIZATION NEEDED XXX
    # OR
    $copy->circ_modifier('ECRL_ILL'); # XXX CUSTOMIZATION NEEDED XXX
    $copy->barcode($barcode);
    $copy->call_number( $vol->{acn_id} );
    $copy->circ_lib(2); # XXX CUSTOMIZATION NEEDED XXX  1 - CONS 2 - ECRL
    $copy->circulate('t');
    $copy->holdable('t');
    $copy->opac_visible('f'); # XXX CUSTOMIZATION NEEDED XXX  't'
    $copy->deleted('f');
    $copy->fine_level(2);
    $copy->loan_duration(2);
    $copy->location(763); # XXX CUSTOMIZATION NEEDED XXX   763 - Interlibrary Loan
    $copy->status($copy_status_id);
    $copy->editor('1');
    $copy->creator('1');

 #   # Add the configured stat cat entries.
 #   my @stat_cats;
 #   my $nodes = $xpath->find("/copy/stat_cat_entry");
 #   foreach my $node ($nodes->get_nodelist) {
 #       next unless ($node->isa('XML::XPath::Node::Element'));
 #       my $stat_cat_id = $node->getAttribute('stat_cat');
 #       my $value = $node->string_value();
 #       # Need to search for an existing asset.stat_cat_entry
 #           my $asce = $e->search_asset_stat_cat_entry({'stat_cat' => $stat_cat_id, 'value' => $value})->[0];
 #       unless ($asce) {
 #           # if not, create a new one and use its id.
 #           $asce = Fieldmapper::asset::stat_cat_entry->new();
 #           $asce->stat_cat($stat_cat_id);
 #           $asce->value($value);
 #           $asce->owner($ou->id);
 #           $e->xact_begin;
 #           $asce = $e->create_asset_stat_cat_entry($asce);
 #           $e->xact_commit;
 #       }
 #       push(@stat_cats, $asce);
 #   }

    $e->xact_begin;
    $copy = $e->create_asset_copy($copy);

 #   if (scalar @stat_cats) {
 #       foreach my $asce (@stat_cats) {
 #           my $ascecm = Fieldmapper::asset::stat_cat_entry_copy_map->new();
 #           $ascecm->stat_cat($asce->stat_cat);
 #           $ascecm->stat_cat_entry($asce->id);
 #           $ascecm->owning_copy($copy->id);
 #           $ascecm = $e->create_asset_stat_cat_entry_copy_map($ascecm);
 #       }
 #   }
    $e->commit;

    return $e->event->{textcode} unless ($r);
    return 'SUCCESS';
}

sub cancel_hold {
    check_session_time();
    my ( $pid, $item_id ) = @_;

    # Check for user
    my $uid = user_id_from_barcode($pid);
    fail('PATRON_BARCODE_NOT_FOUND : ' . $pid) if ( ref($uid) );

    # Check for copy
    my $copy = copy_from_barcode($item_id);
    unless ( defined($copy) && blessed($copy) ) {
        fail('COPY_BARCODE_NOT_FOUND : ' . $item_id);
    }
    my $cid = $copy->id;
    
    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );

    my $holds = $e->search_action_hold_request(
            {   usr => $uid,
                current_copy => $cid,
                fulfillment_time => undef,
                cancel_time => undef
            }
        );

    if ( @$holds ){   
	    my $hid = $holds->[0]->id;
	    my $circ = OpenSRF::AppSession->create('open-ils.circ');
	    my $resp = $circ->request(
               'open-ils.circ.hold.cancel', $session{authtoken}, $hid, 6 )->gather(1); # 6 == patron-cancelled-via-opac
    } 
    return 'SUCCESS';
}

# Checkout a copy to a patron
#
# Arguments
# copy barcode
# patron barcode
#
# Returns
# textcode of the OSRF response.
sub checkout {
    check_session_time();
    my ( $copy_barcode, $patron_barcode, $due_date ) = @_;

    # Check for copy:
    my $copy = copy_from_barcode($copy_barcode);
    unless ( defined($copy) && blessed($copy) ) {
        return 'COPY_BARCODE_NOT_FOUND : ' . $copy_barcode;
    }

    # Check for user
    my $uid = user_id_from_barcode($patron_barcode);
    return 'PATRON_BARCODE_NOT_FOUND : ' . $patron_barcode if ( ref($uid) );

    # Solved mising due date in requested msg
    if ($due_date eq ''){
            my $response = OpenSRF::AppSession->create('open-ils.circ')->request(
                'open-ils.circ.checkout.full.override',
                $session{authtoken},
                {
                    copy_barcode => $copy_barcode,
                    patron_id    => $uid
                }
            )->gather(1);
    }else{
	    my $response = OpenSRF::AppSession->create('open-ils.circ')->request(
	        'open-ils.circ.checkout.full.override',
	        $session{authtoken},
	        {
	            copy_barcode => $copy_barcode,
        	    patron_id    => $uid,
	            due_date     => $due_date
	        }
	    )->gather(1);
    }

    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );

    my $circ = $e->search_action_circulation(
       [ { target_copy => $copy->id, xact_finish => undef } ] )->[0];

    return $circ->due_date;
    #return $response->{textcode};
}

sub renewal {
    check_session_time();
    my ( $copy_barcode, $due_date ) = @_;

    # Check for copy:
    my $copy = copy_from_barcode($copy_barcode);
    unless ( defined($copy) && blessed($copy) ) {
        return 'COPY_BARCODE_NOT_FOUND : ' . $copy_barcode;
    }

    my $response = OpenSRF::AppSession->create('open-ils.circ')->request(
        'open-ils.circ.renew.override',
        $session{authtoken},
        {
            copy_barcode => $copy_barcode,
            due_date     => $due_date
        }
    )->gather(1);
    return $response->{textcode};
}

# Check a copy in
#
# Arguments
# copy barcode
#
# Returns
# "SUCCESS" on success
# textcode of a failed OSRF request
# 'COPY_NOT_CHECKED_OUT' when the copy is not checked out

sub checkin {
    check_session_time();
    my ($barcode) = @_;

    my $copy = copy_from_barcode($barcode);
    return $copy->{textcode} unless ( blessed $copy);

    # Simon: 7/8/2014 Commented the below code, since we want to add copy status 6: In-transit, 0: available, 7: Reshelving back in with 1: checked out.  <<< support check_in for borrowing workflow
    #return ("COPY_NOT_CHECKED_OUT $barcode")
    #  unless ( $copy->status == OILS_COPY_STATUS_CHECKED_OUT );

    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );

    my $circ = $e->search_action_circulation(
        [ { target_copy => $copy->id, xact_finish => undef } ] )->[0];
    my $r =
      OpenSRF::AppSession->create('open-ils.circ')
      ->request( 'open-ils.circ.checkin.override',
        $session{authtoken}, { force => 1, copy_id => $copy->id } )->gather(1);
    return 'SUCCESS' if ( $r->{textcode} eq 'ROUTE_ITEM' );
    return $r->{textcode};
}

# Get actor.usr.id from barcode.
# Arguments
# patron barcode
#
# Returns
# actor.usr.id
# or hash on error
sub user_id_from_barcode {
    check_session_time();
    my ($barcode) = @_;

    my $response;

    my $e = new_editor( authtoken => $session{authtoken} );
    return $response unless ( $e->checkauth );

    my $card = $e->search_actor_card( { barcode => $barcode, active => 't' } );
  
    # not found patron barcode
    fail('PATRON_BARCODE_NOT_FOUND : ' . $barcode) unless (@$card);

    $response = $card->[0]->usr if (@$card);
    $e->finish;

    return $response;
}

# Place a simple hold for a patron.
#
# Arguments
# Target object appropriate for type of hold
# Patron for whom the hold is place
#
# eeturns
# "SUCCESS" on success
# textcode of a failed OSRF request
# "HOLD_TYPE_NOT_SUPPORTED" if the hold type is not supported
# (Currently only support 'T' and 'C')

# simple hold should be removed and full holds sub should be used instead - pragmatic solution only

sub place_simple_hold {
    check_session_time();

    #my ($type, $target, $patron, $pickup_ou) = @_;
    my ( $target, $patron_id ) = @_;

    # NOTE : switch "t" to an "f" to make inactive hold active
    require '/openils/bin/oils_header.pl';    # XXX CUSTOMIZATION NEEDED XXX
    use vars qw/ $apputils $memcache $user $authtoken $authtime /;

 # XXX: local opensrf core conf filename should be in config.
 # XXX: STAFF account with ncip service related permissions should be in config.
    osrf_connect("/openils/conf/opensrf_core.xml");
    oils_login( "username_here", "password_here" );
    my $ahr = Fieldmapper::action::hold_request->new();
    $ahr->hold_type('T');
    # The targeter doesn't like our special statuses, and changing the status after the targeter finishes is difficult because it runs asynchronously.  Our workaround is to create the hold frozen, unfreeze it, then run the targeter manually.
    $ahr->target($target);
    $ahr->usr($patron_id);
    $ahr->requestor(0);     # XXX CUSTOMIZATION NEEDED XXX admin user (?)
    $ahr->pickup_lib(2);    # XXX CUSTOMIZATION NEEDED XXX script user OU
    $ahr->phone_notify(0);
    $ahr->email_notify(0);
    $ahr->frozen('t');
    my $resp = simplereq( CIRC(), 'open-ils.circ.holds.create', $authtoken, $ahr );
    my $e = new_editor( xact => 1, authtoken => $session{authtoken} );
    $ahr = $e->retrieve_action_hold_request($resp);    # refresh from db
    $ahr->frozen('f');
    $e->update_action_hold_request($ahr);
    $e->commit;
    $U->storagereq( 'open-ils.storage.action.hold_request.copy_targeter', undef, $ahr->id );

    #oils_event_die($resp);
    my $errors = "";
    if ( ref($resp) eq 'ARRAY' ) {
        ( $errors .= "error : " . $_->{textcode} ) for @$resp;
        return $errors;
    } elsif ( ref($resp) ne 'HASH' ) {
        return "Hold placed! hold_id = " . $resp . "\n";
    }
}

# Place a hold for a patron.
#
# Arguments
# Type of hold
# Target object appropriate for type of hold
# Patron for whom the hold is place
# OU where hold is to be picked up
#
# Returns
# "SUCCESS" on success
# textcode of a failed OSRF request
# "HOLD_TYPE_NOT_SUPPORTED" if the hold type is not supported
# (Currently only support 'T' and 'C')
# XXX NOT USED OR WORKING, COMMENTING OUT FOR NOW
sub place_hold {
    check_session_time();
    my ( $type, $target, $patron, $pickup_ou ) = @_;

    my $work_ou = '1';  #customize
    #my $ou  = org_unit_from_shortname($work_ou);        # $work_ou is global
    my $ou  = org_unit_from_shortname($pickup_ou);
    #my $ou = $pickup_ou;
    my $ahr = Fieldmapper::action::hold_request->new;
    $ahr->hold_type($type);
    if ( $type eq 'C' ) {
        $ahr->target( $target );
        $ahr->current_copy( $target );
    } elsif ( $type eq 'T' ) {
        $ahr->target($target);
    } else {
        return "HOLD_TYPE_NOT_SUPPORTED";
    }
    $ahr->usr( user_id_from_barcode($patron) );

    $ahr->pickup_lib($ou->id);

    my $e = new_editor( authtoken => $session{authtoken} );
    return $e->event->{textcode} unless ( $e->checkauth );

    my $card = $e->search_actor_user( 
             { id => user_id_from_barcode($patron) });

    my $phone = $card->[0]->day_phone if (@$card);
    # Email Notification for Hold Requests, maybe need to check if patron having email or not
    if ( $type eq 'T' ) {    # request_item msg: don't need to have email notify
      $ahr->email_notify('f');
    } else {
      $ahr->email_notify('t');
    }
    $ahr->phone_notify( $phone ) if ( $phone );

  #  if ( !$patron->email ) {
  #      $ahr->email_notify('f');
  #      $ahr->phone_notify( $patron->day_phone ) if ( $patron->day_phone );
  #  } else {
  #      $ahr->email_notify('t');
  #  }

    # We must have a title hold and we want to change the hold
    # expiration date if we're sending the copy to the VC.
    # set_title_hold_expiration($ahr) if ( $ahr->pickup_lib == '2' );

    my $params = {
        pickup_lib => $ahr->pickup_lib,
        patronid   => $ahr->usr,
        hold_type  => $ahr->hold_type
    };

    if ( $ahr->hold_type eq 'C' ) {
        $params->{copy_id} = $ahr->target;
    } else {
        $params->{titleid} = $ahr->target;
    }

    my $r =
      OpenSRF::AppSession->create('open-ils.circ')
      ->request( 'open-ils.circ.title_hold.is_possible',
        $session{authtoken}, $params )->gather(1);

    if ( $r->{textcode} ) {
        return $r->{textcode};
    } elsif ( $r->{success} ) {
        $r =
          OpenSRF::AppSession->create('open-ils.circ')
          ->request( 'open-ils.circ.holds.create.override',
            $session{authtoken}, $ahr )->gather(1);

        my $returnValue = "SUCCESS";
        if ( ref($r) eq 'HASH' ) {
            $returnValue =
              ( $r->{textcode} eq 'PERM_FAILURE' )
              ? $r->{ilsperm}
              : $r->{textcode};
            $returnValue =~ s/\.override$//
              if ( $r->{textcode} eq 'PERM_FAILURE' );
        }

        usleep(5000000);
        
        my $hold_ID = $r;
        my $e = new_editor( authtoken => $session{authtoken} );
        return $e->event->{textcode} unless ( $e->checkauth );

        my $holds = $e->search_action_hold_request(
        {   id => $hold_ID,
                  fulfillment_time => undef,
                  cancel_time => undef
        });
        my $cp_id = $holds->[0]->current_copy;

        my $copy = $e->search_asset_copy(
        {
            'id' => $cp_id
        })->[0];
    
        # handle error 
        fail('Error in place hold for this Item - Copy ID : ' . $cp_id) unless ($copy);

        return $copy->barcode;

    } else {
        return 'HOLD_NOT_POSSIBLE';
    }
}

# Set the expiration date on title holds
#
# Argument
# Fieldmapper action.hold_request object
#
# Returns
# Nothing
# XXX NOT USED OR WORKING, COMMENTING OUT FOR NOW
#sub set_title_hold_expiration {
#    my $hold = shift;
#    if ( $title_holds->{unit} && $title_holds->{duration} ) {
#        my $expiration = DateTime->now( time_zone => $tz );
#        $expiration->add( $title_holds->{unit} => $title_holds->{duration} );
#        $hold->expire_time( $expiration->iso8601() );
#    }
#}

# Get actor.org_unit from the shortname
#
# Arguments
# org_unit shortname
#
# Returns
# Fieldmapper aou object
# or HASH on error
sub org_unit_from_shortname {
    check_session_time();
    my ($shortname) = @_;
    my $ou =
      OpenSRF::AppSession->create('open-ils.actor')
      ->request( 'open-ils.actor.org_unit.retrieve_by_shortname', $shortname )
      ->gather(1);
    return $ou;
}

# Flesh user information
# Arguments
# actor.usr.id
#
# Returns
# fieldmapped, fleshed user or
# event hash on error
sub flesh_user {
    check_session_time();
    my ($id) = @_;
    my $response =
      OpenSRF::AppSession->create('open-ils.actor')
      ->request( 'open-ils.actor.user.fleshed.retrieve',
        $session{'authtoken'}, $id,
        [ 'card', 'cards', 'standing_penalties', 'home_ou', 'profile' ] )
      ->gather(1);
    return $response;
}
