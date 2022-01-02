---
title: "Dbcli"
date: 2020-02-29T18:45:51-05:00
draft: false
tags: ["Python", "DB"]
---

The [DBLCI](https://www.dbcli.com/) project creates command line database clients with auto-completion and syntax highlighting. These clients are often nicer to work with than the one a database comes with. In this post we're going to demo the [LiteCLI](https://litecli.com/) client.

First to install,

```bash
pip install litecli
```

I created a sqlite database and populated it with the following code

```sqlite
.open test.db

CREATE TABLE Users (
  UserID INTEGER PRIMARY KEY,
  firstName TEXT NOT NULL,
  lastName TEXT NOT NULL
);

INSERT INTO Users (firstName, lastName) VALUES ("Pearl", "Perez");
INSERT INTO Users (firstName, lastName) VALUES ("Derrick", "Norton");
INSERT INTO Users (firstName, lastName) VALUES ("Joan", "Daniels");
INSERT INTO Users (firstName, lastName) VALUES ("Marian", "Lane");
INSERT INTO Users (firstName, lastName) VALUES ("Roland", "Gregory");
INSERT INTO Users (firstName, lastName) VALUES ("Charlene", "Baldwin");
INSERT INTO Users (firstName, lastName) VALUES ("Lester", "Kennedy");
INSERT INTO Users (firstName, lastName) VALUES ("Dan", "Vasquez");
INSERT INTO Users (firstName, lastName) VALUES ("Genevieve", "Dean");
INSERT INTO Users (firstName, lastName) VALUES ("Sue", "Bennett");
```

Now let's open it up using `litecli` and show the syntax highlighting.

![image-20200229185045757](/files/images/20200229185045757.png)