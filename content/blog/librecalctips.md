---
date: 2021-02-20 17:37:48
draft: false
medium_enabled: true
medium_post_id: c55df201e882
tags: []
title: LibreOffice Calc Tips
---

I've been working with LibreOffice Calc (or Excel) spreadsheets recently and wanted to share some of the things I've learned.

**Absolute vs Relative Cell References**

The main difference between referencing a cell relatively vs absolute is that the absolute reference includes a `$` in the front. This is important if you want to drag a formula across multiple cells.

```excel
$A:$B
```

**Referring to a sheet name**

To refer to cells in another sheet, first begin the reference with the sheet name, then a period, follow by the cells you wish to reference in that sheet. If the sheet name has spaces in it, then you need to wrap it in quotes.

```excel
'Another Sheet'.A:B
```

**Referring to a column**

To refer to a single column, you need to repeat the column name separated by a colon.

```excel
B:B
```

**Get row that matches a query**

For this we'll use the `MATCH` function. It takes three parameters:

1. The value to match
2. The range of cells to query over
3. Which comparison function to use. Use `0` for equality.

It will then return the first row number that matches the query.

```excel
MATCH("Bob", B:B, 0)
```

**Query a value based on another from that row.**

To do this, we will need to combine both the `INDEX` function and the `MATCH` function. The `INDEX` function takes three parameters:

1. The range of cells to reference
2. The row number
3. The column number

Use the `MATCH` function as the second argument, and you can reference another column of a row based on a query.

```excel
INDEX(A:B, MATCH("Bob", B:B, 0), 1)
```

**Refer to a value in a nearby cell**

With the `OFFSET` function you can refer to a cell relative to another. Its parameters are:

1. Reference Cell
2. Row Offset
3. Column Offset
4. Height
5. Width

```excel
# To see the value in the row above A5 (A4)
OFFSET(A5, -1, 0, 1, 1)
```

**Concatenate Strings**

Strings separated by `&` are concatenated together.

```excel
"Hello " & "World."
```