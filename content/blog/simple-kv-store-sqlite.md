---
title: "Simple Key-Value Store using Sqlite3"
date: 2023-11-09T22:15:23-05:00
draft: false
tags: ["DB"]
math: false
medium_enabled: false
---

A lot of software nowadays are built for scale. You have to setup a Kubernetes cluster and deploy Redis for duplication in order to have a key-value store. Though for many small projects, I feel like it's overkill. 

I'll show in this post, that we can have a nice simple[^1] key-value store using `sqlite3`[^2]. This gives us the benefit that we don't need to use system resources to run a daemon the entire time and only spin up a process when we need it.

For our key-value store, we're going to use a table with two columns:

- A key, which we'll call `name`. This will be a unique `TEXT` type that has to be set.
- The value, which we'll call `value` (Creative, I know.) For our purposes, this will also be a `TEXT` type.

The SQL to create this table is[^3]

```sql
CREATE TABLE config(
    name TEXT NOT NULL,
    value TEXT
);
```

Let's say we want to get the value of the key `author`. This is a `SELECT` statement away:

```sql
SELECT value FROM config where name='author';
```

Now let's say that we want to insert a new key into the table.

```sql
INSERT INTO config(name, value) VALUES ('a', '1');
```

What about updating?

```sql
UPDATE config SET value='2' WHERE name='a';
```

The tricky part is if we want to insert if the key does not exist, and update if it does. To handle this we'll need to resolve the [conflict](https://www.sqlite.org/lang_conflict.html).

```sql
INSERT INTO config(name, value) VALUES ('a', '3') ON CONFLICT(name) DO UPDATE SET value=excluded.value;
```

Lastly if you want to export the entire key-value store as a CSV:

```bash
sqlite3 -header -csv data.db "SELECT * FROM config;"
```

This is nice and all, but it's inconvinient to type out all these SQL commands. Therefore, I wrote two little bash scripts.

**`sqlite3_getkv`**

```bash
#!/bin/sh

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: sqlite3_getkv [db_file] [key]"
    exit 1
}

# Check argument count
if [ "$#" -ne 2 ]; then
    show_usage
fi

# Initalize database file is not already
sqlite3 "$1" "CREATE TABLE IF NOT EXISTS config(name TEXT NOT NULL UNIQUE, value TEXT);"

# Get value from key
sqlite3 "$1" "SELECT value FROM CONFIG where name='$2';"

```

**`ssqlite3_setkv`**

```bash
#!/bin/sh

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
    echo "Usage: sqlite3_setkv [db_file] [key] [value]"
    exit 1
}

# Check argument count
if [ "$#" -ne 3 ]; then
    show_usage
fi

# Initalize database file is not already
sqlite3 "$1" "CREATE TABLE IF NOT EXISTS config(name TEXT NOT NULL UNIQUE, value TEXT);"

# Set key-value pair
sqlite3 "$1" "INSERT INTO config(name, value) VALUES ('$2', '$3') ON CONFLICT(name) DO UPDATE SET value=excluded.value;"
```

**Example Usage:**

```
$ ./sqlite3_setkv.sh test.db a 4
$ ./sqlite3_setkv.sh test.db c 5
$ ./sqlite3_getkv.sh test.db a
4
$ ./sqlite3_setkv.sh test.db a 5
$ ./sqlite3_getkv.sh test.db a
5
```

[^1]: Somehow my idea of easier, simpler, and more maintainable is writing bash scripts.
[^2]: Justin pointed out that the [CPython implementation](https://github.com/python/cpython/blob/a15a584bf3f94ea11ab9363548c8872251364000/Lib/dbm/sqlite3.py#L7) works similarly.
[^3]: Unfortantely, we can't only use the `PRIMARY KEY` qualifier for the name field as sqlite has a [historical quirk](https://www.sqlite.org/quirks.html) which allows primary keys to be null. 

