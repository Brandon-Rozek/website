---
id: 2198
title: Java Swing Components
date: 2017-06-05T23:30:18+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=2198
aliases:
    - /2017/06/java-swing-components/
permalink: /2017/06/java-swing-components/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
mf2_syndicate-to:
  - 'a:1:{i:0;s:4:"none";}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
tumblr_post_id:
  - "161484582559"
kind:
  - article
tags: ["Java"]
---
This post, over time, will serve as a reference to myself and others of the different UI components available in the Swing library. This post assumes a general familiarity with setting up a basic Swing application and focuses only on the individual components.

<!--more-->

### Buttons

Buttons are created using the JButton component. The constructor takes the text placed inside the button.

<pre class='language-java'><code class='language-java'>
JButton stopBtn = new JButton("Stop");
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/stopbutton.png" alt="" width="67" height="25" class="alignnone size-full wp-image-2211" /> 

You can also add images inside a button. To do that you need to get the image and make it into an icon. The following code grabs the image file &#8220;smallpanda.jpg&#8221; from the current working directory.

<pre class='langauge-java'><code class='language-java'>
Image img = this.getImage(this.getCodeBase(), "smallpanda.jpg");
ImageIcon imgIcon = new ImageIcon(img);
JButton feedBtn = new JButton("Feed", imgIcon);
</code></pre>

Sometimes, you want to change the location of the text in the button. Like say, we want to place the text in the center horizontally and bottom vertically.

<pre class='language-java'><code class='language-java'>
feedBtn.setHorizontalTextPosition(JButton.CENTER);
feedBtn.setVerticalTextPosition(JButton.BOTTOM);
</code></pre>

Don&#8217;t forget to add your buttons to the screen!

<pre class='language-java'><code class='language-java'>
this.add(stopBtn);
this.add(feedBtn);
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/smallpandabutton.png" alt="" width="234" height="181" class="alignnone size-full wp-image-2210" /> 

### Labels and Textfields

One of the most common forms of input is a text field, usually distinguished with a label. Those components are called JTextField and JLabel respectively. The constructor for JTextArea can take just the width of the text field, or another common use is to have already inputed text and its width.

<pre class='language-java'><code class='language-java'>
    JLabel nameLabel = new JLabel("Enter in your name: ");

    // Create an input and set the width to be 10px wide
    JTextField nameInput = new JTextField(10);
    //Override nameInput with a field already contains the text "Brandon"
    //And is 10px wide
    nameInput = new JTextField("Brandon", 10);
    
    this.add(nameLabel);
    this.add(nameInput);
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/labeltextfield.png" alt="" width="274" height="24" class="alignnone size-full wp-image-2209" /> 

### Checkboxes

Checkboxes are commonly used when giving the possibility for multiple answers. Such as, check all of the foods that you like.

<pre class='language-java'><code class='language-java'>
    JCheckBox pizza = new JCheckBox("Pizza");
    JCheckBox noodles = new JCheckBox("Noodles");
    JCheckBox rice = new JCheckBox("Rice");
    this.add(pizza);
    this.add(noodles);
    this.add(rice);
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/checkboxes.png" alt="" width="206" height="40" class="alignnone size-full wp-image-2207" /> 

You can even replace the default look of the checkbox with an image. To do this, you need to make image icons for both when it&#8217;s checked and when it&#8217;s unchecked.

<pre class='language-java'><code class='language-java'>
Image checkedImage = this.getImage(this.getCodeBase(), "checked.png");
Image uncheckedImage = this.getImage(this.getCodeBase(), "unchecked.png");

ImageIcon checkedIcon = new ImageIcon(checkedImage);
ImageIcon uncheckedIcon = new ImageIcon(uncheckedImage);

JCheckBox checkbox = new JCheckBox("Check Me", uncheckedIcon);
checkbox.setSelectedIcon(checkedIcon);

this.add(checkbox);
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/unchecked.png" alt="" width="187" height="123" class="alignnone size-full wp-image-2213" />  
<img src="https://brandonrozek.com/wp-content/uploads/2017/06/checked.png" alt="" width="186" height="102" class="alignnone size-full wp-image-2208" /> 

### Text Areas

Text Areas are different from text fields in which it is made to be able to hold multiple lines of text. It&#8217;s called JTextArea and its construction takes a width and height as it&#8217;s arguments.

<pre class='language-java'><code class='language-java'>
JTextArea textarea = new JTextArea(10, 10);
</code></pre>

By default, when the someone inputs more text than the size can hold, it will automatically grow with the text inputted. To override this behaviour and instead introuduce scroll bars. One must define a ScrollPane and put the TextArea inside of it by using it as the scroll pane&#8217;s argument for its constructor.

<pre class='language-java'><code class='language-java'>
JScrollPane scrollPane = new JScrollPane(textarea);
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/textarea.png" alt="" width="119" height="149" class="alignnone size-full wp-image-2212" /> 

### Radio Buttons

Radio buttons are used for when you only want one out of many different options to be selected. For this, one needs to define a button group that houses the radio buttons for the user to choose from. This can be achieved with ButtonGroup and JRadioButton respectively.

<pre class='language-java'><code class='language-java'>
// Make the radio buttons
JRadioButton radio1 = new JRadioButton("Pies");
JRadioButton radio2 = new JRadioButton("Cakes");
JRadioButton radio3 = new JRadioButton("Cookies");

// Put the radio buttons in a group
Button Group desserts = new ButtonGroup();
desserts.add(radio1);
desserts.add(radio2);
desserts.add(radio3);

// Add the radio buttons to the screen
this.add(radio1);
this.add(radio2);
this.add(radio3);
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/radiobuttons.png" alt="" width="211" height="34" class="alignnone size-full wp-image-2218" /> 

### JList

To display a list of items that are clickable by the user, you can use a `JList`. JLists require a model that stores the list implementation, we&#8217;ll use `DefaultListModel` to achieve this purpose.

<pre class='language-java'><code class='language-java'>
DefaultListModel model = new DefaultListModel();
JList list = new JList(model);
</code></pre>

To add scrolling capabilities, remember to add it to a scroll pane

<pre class='language-java'><code class='language-java'>
JScollPane sp = new JScrollPane(list);
</code></pre>

You can set the number of items you wish to see in the list. The example below, allows us to see three items in the list.

<pre class='language-java'><code class='language-java'>
list.setVisibleRowCount(3);
</code></pre>

There are a variety of ways to add items to the list. If a number is specified that tells it to place it at the index specified. Starting from the top at zero, to the button.

<pre class='language-java'><code class='language-java'>
model.addElement("Apples")
model.addElement("Cherries");
model.addElement("Bananas");
// Adds 'Oranges' to the top
model.add(0, "Oranges");
</code></pre>

Sometimes, you want to only let the user select one item. At the end, don&#8217;t forget to add the component to the screen!

<pre class='language-java'><code class='language-java'>
list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
this.add(sp);
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/JList.png" alt="" width="77" height="53" class="alignnone size-full wp-image-2224" /> 

### JComboBox

To create a dropdown list of different options, consider using a JComboBox.

<pre class='language-java'><code class='language-java'>
JComboBox cb = new JComboBox();
cb.addItem("Select Food Option");
cb.addItem("Pizza");
cb.addItem("Burger");
cb.addItem("Hot Dog");
cb.addItem("Steak");
// Add it to the screen
this.add(cb);
</code></pre>

<img src="https://brandonrozek.com/wp-content/uploads/2017/06/JComboBox.png" alt="" width="153" height="24" class="alignnone size-full wp-image-2223" srcset="https://brandonrozek.com/wp-content/uploads/2017/06/JComboBox.png 153w, https://brandonrozek.com/wp-content/uploads/2017/06/JComboBox-150x24.png 150w" sizes="(max-width: 153px) 100vw, 153px" />