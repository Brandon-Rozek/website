---
title: "QTcpSocket"
date: 2020-03-20T16:21:07-04:00
draft: false
tags: ["C++", "Qt"]
---

There are two ways that I can think of for checking if a TCP socket times out in Qt. You can either use `waitForConnected` or a `QTimer`.  The Qt 5.14 documentation noted that the `waitForConnected` call may randomly fail in Windows.

Here is some shared code for both examples

```c++
QTcpSocket *socket = new QTcpSocket(this);
quint16 listenPort = 4444;
int timeout = 1000; // Units: milliseconds
QHostAddress destination("192.168.0.2");
```



## `waitForDisconnected`

Let's say that we have a `QTcpScoket` pointer named `socket`. 

```c++
socket->connectToHost(destination, listenPort);
if (!socket->waitForConnected(timeout)) {
    qDebug("Connection Timed Out.");
}
```

Notes:

- `waitForConnected` is a blocking call
- This does not account for the host lookup call.

## `QTimer`

This method requires a little more setup. Let's assume we have a class named `Test` that inherits `QObject`.

```c++
// ....
socket->connectToHost(destination, listenPort);
timeoutTimer = new QTimer(this);
timeoutTimer->setInterval(timeout);
timeoutTimer->setSingleShot(true);
connect(timeoutTimer, &QTimer::timeout, this, &Test::timeout);
timeoutTimer->start();
// ....

void Test::timeout(void) {
    qDebug("Connected Timed Out.");
    socket->disconnectFromHost();
}
```

Notes:

- This method acts asynchronously

In order for the the timeout function to not always hit, we need to make sure we stop the timer when data is received or a TCP error occurs

```c++
timeoutTimer->stop();
```

