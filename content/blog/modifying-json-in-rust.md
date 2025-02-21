---
title: "Modifying JSON in Rust"
date: 2024-08-03T07:59:15-07:00
draft: false
tags: ["Rust"]
math: false
medium_enabled: false
---

For my new role, I've been learning Rust. I don't know why I didn't learn it earlier, I enjoy it so much that I decided to power my [toots](/toots) page with it.

When I query my toots, I receive a JSON response like the following:

```json
[{"id": "112581869512127927", ..., "content": "...",}, ...]
```

Some parts of the JSON response changes quite frequently. Since I [archive](https://brandonrozek.com/blog/archiving-toots/) the changes, I want to strip out the highly dynamic information before saving it off to a file.

```rust
let mut json_response: serde_json::Value = serde_json::from_str("...")
	.expect("JSON parse error");
```

In order to modify this variable, we need to have some knowledge of it's structure. I'll show in this post how to modify our JSON data given whether we're working with a JSON array or a JSON object.

## `serde_json::Value::Array`

Our example JSON starts off as an array, so let's extract that out:

```rust
let json_array = json_response
	.as_array_mut()
	.expect("Expected JSON Array");
```

The `as_array_mut` says to interpret the `json_response` variable as an array.  The `mut` component is important for us to be able to edit the data in place without making copies.

The `as_array_mut` method returns an option type. Calling `.expect(...)` on it will cause the program to crash if it isn't indeed an array. We can alternatively perform some error handling:

```rust
if let Some(json_array) = json_response.as_array_mut() {
    // Do something with json_array
} else {
    // Error handling here
}
```

Though I'll assume that you're following best practices and not discuss more about error handling in this post.

Our variable `json_array` has type `&mut Vec<serde_json::Value>`which means we can do things like add another element to said array.

```rust
let new_element = serde_json::Value::from(1);
json_array.push(new_element);
```

We can also remove the last element of the array if it exists

```rust
json_array.pop()
```

## `serde_json::Value::Object`

Within the array, we have a list of objects. Let us grab the first element as an example:

```rust
let first_item = json_array.get_mut(0).unwrap();
```

In order to be able to modify the data, we use the `get_mut` method. This, like before, returns an option if it doesn't exist. We can call `unwrap` on it to get access to the data or panic if the element doesn't exist.

The variable `first_item` has type `serde_json::Value`. To interpret this as an object, we need to call `as_object_mut`.

```rust
let first_item_obj = first_item.as_object_mut().unwrap();
```

Now our variable `first_item_obj` has type `&mut Map<String, serde_json::Value>`.

We can remove any fields that we don't think is important

```rust
first_item_obj.remove("bot");
```

Add any fields we want

```rust
let new_key = "PoweredBy".to_string();
let new_value = serde_json::Value::from("Rust");
toot.insert(new_key, new_value);
```

Renaming a field is the combination of the last two:

```rust
let toot_date = toot.remove("created_at")
	.expect("Missing created_at");
toot.insert("date".to_string(), toot_date);
```

