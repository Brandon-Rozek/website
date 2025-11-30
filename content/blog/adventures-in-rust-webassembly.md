---
title: "Adventures in Rust WebAssembly"
date: 2025-02-21T10:13:17-05:00
draft: false
tags:
    - WebAssembly
    - Rust
math: false
medium_enabled: false
---

For two years now, my friend and colleague [James Oswald](https://jamesoswald.dev) has told me to check out [WebAssembly](https://webassembly.org/). I avoided it all this time because I thought it would be too complicated to get started with. In one of our study sessions, my friends Chris and Ethan both said they wanted to look into it. I have to say, that getting started with WebAssembly is far simpler than I've previously imagined and it makes me wish I listened to James earlier.

In this post, I'll show how to use Rust + Webassembly to create both a CLI application and a Web application. [The Rust and Webassembly Book](https://rustwasm.github.io/docs/book/) is a great resource, however like [Diego](https://dzfrias.dev/blog/rust-wasm-minimal-setup/), I found the recommended setup to be a bit too heavy for my liking. I'll do anything to avoid using `npm` in personal projects. 

### Setup

I assume that you have the [`rustup`](https://www.rust-lang.org/tools/install) command available.

First, we'll need to have the `wasm` toolchains installed.

- For CLI applications: `rustup target add wasm32-wasi`
- For Web applications: `rustup target add wasm32-unknown-unknown`

For the web, we'll also need `wasm-bindgen` to create the JavaScript glue code which ingests the `.wasm` file.

```bash
cargo install wasm-bindgen-cli
```

Now we can create our Rust project!

```bash
cargo new rustwasm
```

This will create the following directory structure

```
rustwasm
├── Cargo.toml
└── src
    └── main.rs
```

To compile WebAssembly for the Web, edit the `Cargo.toml` to set the crate-type and add the dependencies.

```toml
[package]
name = "rustwasm"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
wasm-bindgen = "0.2.84"
js-sys = "0.3.77"
```

In the following Rust examples, there will be snippets of `wasm_bindgen` scattered about. This is to create the JavaScript glue code. If you're only running on the CLI then those lines are not needed, but it doesn't hurt to include them.

Let's add a greeter function that returns the string `"Hello World"` in `src/lib.rs`

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn greeting() -> String {
    return String::from("Hello World");
}
```

### CLI Application

For our CLI application, we'll create a `main` function that calls our new `greeting` function. This will live in `src/main.rs`

```rust
use rustwasm;

fn main() {
    let _args = std::env::args();
    println!("{}", rustwasm::greeting());
}
```

I include the `_args` variable to show how you would obtain the command-line arguments, however we won't do anything with those in this example.

To run this in the CLI, we first need to compile the `wasm` file.

```bash
cargo build --target wasm32-wasi --release
```

Then we can use [`wasmtime`](https://wasmtime.dev/) to execute the file

```bash
wasmtime target/wasm32-wasi/release/rustwasm.wasm
```

Feel free to distribute `rustwasm.wasm` among your friends to run on their machines as well!

### Web application

Now let's show how we would run this in the web! First let's create a `public` folder at the base of the Rust project which we'll use to host the website code.

```bash
mkdir public
```

Within `public/index.html` include the following:

```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>Hello wasm!</title>
  </head>
  <body>
    <script type="module" src="index.js"></script>
  </body>
</html>
```

*Note the `type="module"` within the script tag.*

The JavaScript code we have to write luckily is minimal since `rust-bindgen` does the majority of the work for us. Note that we're not running the`main` function within `main.rs`. Instead, we only have access to the methods, structs, etc that are public and annotated with `#[rust_bindgen]` beforehand.

Recall in `lib.rs` that we have the `greeting` function. We would incorporate that into our web application through the following code within `public/index.js`

```javascript
import init, * as wasm from "./rustwasm.js";
await init();

console.log(wasm.greeting());
```

Now, we need to compile our codebase and use `wasm-bindgen` to generate the glue code.

```bash
cargo build --target wasm32-unknown-unknown --release
wasm-bindgen target/wasm32-unknown-unknown/release/rustwasm.wasm --out-dir public --target web
```

*Note: Everytime you update your Rust code, you'll need to run both those commands*

To test this, we can quickly spin up a Python web server.

```bash
cd public
python -m http.server
```

By default your web application would be served at https://localhost:8000. If you open up your console and refresh, you should see the `"Hello World"` message printed.

## More Web Examples

Through the magic of `wasm-bindgen`, we were able to create a function in Rust that returns a string, and without having to think about the internals of Webassembly, get a JavaScript string on the other side. 

The primary usecase of WebAssembly in my mind, is to offload heavier computations. You can edit the DOM directly using the [`web-sys`](https://rustwasm.github.io/wasm-bindgen/api/web_sys/) crate. However, I'll focus my remaining examples and getting data in and out of the compiled Rust code.

**Example:** Calling a Rust-wasm function with a primitive argument

Let's create a small Rust function that takes an integer and outputs the integer plus one.

```rust
#[wasm_bindgen]
pub fn plusone(x: i32) -> i32 {
    x + 1
}
```

Remember to mark the function as public (`pub`) and annotate it with `#[wasm_bindgen]` in order for it to be available in the JavaScript.

Recompile the Rust code using the two commands from earlier, and edit the `public/index.js` function to log an example output of the function.

```javascript
console.log(wasm.plusone(5))
```

Be careful with what primitive types we use in Rust. If you were to change `i32` to `u32` and call the function in JavaScript with a negative number, then the Rust Wasm side will reinterpret the negative number as a large `u32`.

**Example:** Taking in arbitrary JavaScript values (Dictionaries, arrays, etc.)  

Using the [`js-sys`](https://rustwasm.github.io/wasm-bindgen/api/js_sys/index.html) crate, we can take an arbitrary JavaScript value as a parameter and use the `Reflect` module to access field names or interpret the data.

```rust
#[wasm_bindgen]
pub fn get_name(obj: JsValue) -> String {
    let key = JsValue::from_str("name");
    let value_option = js_sys::Reflect::get(&obj, &key)
        .ok()
        .and_then(|v| v.as_string());
    value_option.unwrap_or_else(|| String::from("Error encountered"))
}
```

In the example above, we take a JavaScript value called `obj` and attempt to access the `name` field as a string. Since `obj` can be any arbitrary JavaScript value, we need to include error handling within our code. There are three possible error conditions:

- `obj` is not a JavaScript object (within `js_sys::Reflect::get`)
- `"name"` is not a field in the object (also within `js_sys::Reflect::get`)
- `obj.name` is not a string (within `.as_string()`)

It's a little burdensome to write this code. But given that JavaScript isn't a typed language, it's amazing we can process arbitrary JavaScript values at all.

**Example:** Returning a `struct` from Rust-wasm

Say we have a `Person` struct.

```rust
#[wasm_bindgen]
pub struct Person {
    name: String,
    age: u32,
}
```

In order for this struct to be accessible in the JavaScript, we'll need to make it public (`pub`) and add the `#[wasm_bindgen]` annotation.

Additionally, JavaScript objects have constructors and getter functions. We'll need to implement those publicly within Rust and add the right annotations.

```rust
#[wasm_bindgen]
impl Person {
    #[wasm_bindgen(constructor)]
    pub fn new(name: String, age: u32) -> Person {
        Person { name, age }
    }
     
    // Getter for name field
    pub fn name(&self) -> String {
        self.name.clone()
    }
    
    // Getter for the age field
    pub fn age(&self) -> u32 {
        self.age
    }
}
```

Lastly, let's create a small function that returns a  specific `Person` struct.

```rust
#[wasm_bindgen]
pub fn bob() -> Person {
    return Person::new(String::from("Bob"), 22)
}
```

Now within `public/index.js`, we can call `wasm.bob()` and bring over the new person object. From there, we can access its fields using the getter methods.

```javascript
const person = wasm.bob();
console.log("Name: " + person.name() + ", Age: " + person.age);
```

That's all for today! From here the world is our oyster. We can leverage the type safe and efficient properties of Rust and write code that's not only available on the Web, but also through the CLI; all while being architecture-independent. 







