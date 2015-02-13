iNCIPit (supporting version 2.0)
=======

A branch of iNCIPit : Inital version of ncip v.2 ncip responder for evergreen / open-ils

PALS has been working on iNCIPit to make it work for East Central Regional Library (ECRL) Evergreen and MnLINK Gateway via the NCIP protocol version 2.0.

We fixed 5 messages: RequestItem, CheckOutItem, CheckInItem, AcceptItem, and CancelRequestItem

Initial configuration
---------------------

Setup the default configuration file:

```
cp iNCIPit-example.ini iNCIPit.ini # edit as necessary
```

Optionally, per request hostname configuration files can be used. For example:

- https://target.host/iNCIPit.cgi # REQUEST URL
- target.host # HOSTNAME
- target.host.ini # CONFIGURATION FILE

```
cp iNCIPit-example.ini target.host.ini # edit as necessary
```

Testing
-------

you can initiate / test with the following:

```
curl -v --insecure -H 'Content-Type:text/xml' --data @NCIPmsgs/LookupUser.ncip -X POST 'https://target.host/iNCIPit.cgi'
# (--insecure argument only necessary if you test a target.host lacking a valid cert) 
```

---
