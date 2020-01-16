---
id: 2250
title: Identifying Misspelled Words in your Dataset with Hunspell
date: 2018-01-22T05:17:16+00:00
author: rozek_admin
layout: post
guid: https://brandonrozek.com/?p=2250
permalink: /2018/01/identifying-misspelled-words-dataset-hunspell/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:75:"https://cdn-images-1.medium.com/fit/c/200/200/1*06lotWcLMUnKZTN6-Th3IQ.jpeg";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"c0ccd543b7e6";s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:104:"https://medium.com/@brandonrozek/identifying-misspelled-words-in-your-dataset-with-hunspell-c0ccd543b7e6";}'
mf2_mp-syndicate-to:
  - 'a:1:{i:0;s:22:"bridgy-publish_twitter";}'
tumblr_post_id:
  - "169988632939"
mf2_syndication:
  - 'a:1:{i:0;s:60:"https://twitter.com/B_RozekJournal/status/955308388384235521";}'
kind:
  - article
---
This article is based on one written by [Markus Konrad](https://datascience.blog.wzb.eu/author/markus_konrad/) at this link <a href='https://datascience.blog.wzb.eu/2016/07/13/autocorrecting-misspelled-words-in-python-using-hunspell/' target='_blank' >https://datascience.blog.wzb.eu/2016/07/13/autocorrecting-misspelled-words-in-python-using-hunspell/</a>

I assume in this article that you have hunspell and it's integration with python installed. If not, please refer to the article mention above and follow the prerequisite steps.

This article is inspired from the need to correct misspelled words in the [Dress Attributes Dataset](https://archive.ics.uci.edu/ml/datasets/Dresses_Attribute_Sales). I'll share with you my initial pitfall, and what I ended up doing instead.

### Background Information

Misspelled words are common when dealing with survey data or data where humans type in the responses manually. In the Dress Attributes Dataset this is apparent when looking at the sleeve lengths of the different dresses.

<pre><code class='language-python' lang='python'>dresses_data[&#39;SleeveLength&#39;].value_counts()
</code></pre><figure> 

| Word           | Frequency |
| -------------- | --------- |
| sleevless      | 223       |
| full           | 97        |
| short          | 96        |
| halfsleeve     | 35        |
| threequarter   | 17        |
| thressqatar    | 10        |
| sleeveless     | 5         |
| sleeevless     | 3         |
| capsleeves     | 3         |
| cap-sleeves    | 2         |
| half           | 1         |
| Petal          | 1         |
| urndowncollor  | 1         |
| turndowncollor | 1         |
| sleveless      | 1         |
| butterfly      | 1         |
| threequater    | 1         |</figure> 

Ouch, so many misspelled words. This is when my brain is racking up all the ways I can automate this problem away. Hence my stumbling upon Markus' post.

### Automagically Correcting Data

First, I decided to completely ignore what Markus warns in his post and automatically correct all the words in that column.

To begin the code, let's import and create an instance of the spellchecker:

<pre><code class='language-python' lang='python'>from hunspell import HunSpell
spellchecker = HunSpell(&#39;/usr/share/hunspell/en_US.dic&#39;, &#39;/usr/share/hunspell/en_US.aff&#39;)
</code></pre>

I modified his `correct_words` function so that it only corrects one word and so I can `apply` it along the `SleeveLength` column. 

<pre><code class='language-python' lang='python'>def correct_word(checker, word, add_to_dict=[]):
    "Takes in a hunspell object and a word and corrects the word if needed"   
    # Add custom words to the dictionary
    for w in add_to_dict:
        checker.add(w)

    corrected = ""
    # Check to see if it&#39;s a string
    if isinstance(word, str):
        # Check the spelling
        ok = checker.spell(word)
        if not ok:
            # Grab suggestions for misspelled word
            suggestions = checker.suggest(word)
            if suggestions:
                # Grab the best suggestion
                best = suggestions[0]
                corrected = best
            else:
                # There are no suggestions for misspelled word, return the original
                corrected = word 
        else:
            # Word is spelled correctly
            corrected = word
    else:
        ## Not a string. Return original
        corrected = word
    return corrected
</code></pre>

Now let's apply the function over the `SleeveLength` column of the dataset:

<pre><code class='language-python' lang='python'>dresses_data[&#39;SleeveLength&#39;] = dresses_data[&#39;SleeveLength&#39;].apply(
    lambda x: correct_word(spellchecker, x))
</code></pre>

Doing so creates the following series:<figure> 

| Word           | Frequency |
| -------------- | --------- |
| sleeveless     | 232       |
| full           | 97        |
| short          | 96        |
| half sleeve    | 35        |
| three quarter  | 17        |
| throatiness    | 10        |
| cap sleeves    | 3         |
| cap-sleeves    | 2         |
| Petal          | 1         |
| butterfly      | 1         |
| turndowncollor | 1         |
| half           | 1         |
| landownership  | 1         |
| forequarter    | 1         |</figure> 

As you might be able to tell, this process didn't go as intended. `landownership` isn't even a length of a sleeve!

### Reporting Misspelled Items and Allowing User Intervention

This is when I have to remember, technology isn't perfect. Instead we should rely on ourselves to identify what the word should be correctly spelled as.

Keeping that in mind, I modified the function again to take in a list of the data, and return a dictionary that has the misspelled words as the keys and suggestions as the values represented as a list.

<pre><code class='language-python' lang='python'>def list_word_suggestions(checker, words, echo = True, add_to_dict=[]):
    "Takes in a list of words and returns a dictionary with mispellt words as keys and suggestions as a list. Also prints it out"
    # add custom words to the dictionary
    for w in add_to_dict:
        checker.add(w)
    
    suggestions = {}
    for word in words:
        if isinstance(word, str):
            ok = checker.spell(word)
            if not ok and word not in suggestions:
                suggestions[word] = checker.suggest(word)
                if not suggestions[word] and echo:
                    print(word + ": No suggestions")
                elif echo:
                    print(word + ": " + "[", ", ".join(repr(i) for i in suggestions[word]), "]")
    return suggestions
</code></pre>

With that, I can use the function on my data. To do so, I convert the pandas values to a list and pass it to the function:

<pre><code class='language-python' lang='python'>s = list_word_suggestions(spellchecker, dresses_data[&#39;SleeveLength&#39;].values.tolist())
</code></pre>

These are the suggestions it produces:

<pre><code class='language-python' lang='python'>sleevless: [ &#39;sleeveless&#39;, &#39;sleepless&#39;, &#39;sleeves&#39;, &#39;sleekness&#39;, &#39;sleeve&#39;, &#39;lossless&#39; ]
threequarter: [ &#39;three quarter&#39;, &#39;three-quarter&#39;, &#39;forequarter&#39; ]
halfsleeve: [&#39;half sleeve&#39;, &#39;half-sleeve&#39;, &#39;sleeveless&#39; ]
turndowncollor: No suggestions
threequater: [ &#39;forequarter&#39; ]
capsleeves: [ &#39;cap sleeves&#39;, &#39;cap-sleeves&#39;, &#39;capsules&#39; ]
sleeevless: [ &#39;sleeveless&#39;, &#39;sleepless&#39;, &#39;sleeves&#39;, &#39;sleekness&#39;, &#39;sleeve&#39; ]
urndowncollor: [ &#39;landownership&#39; ]
thressqatar: [ &#39;throatiness&#39; ]
sleveless: [ &#39;sleeveless&#39;, &#39;levelness&#39;, &#39;valveless&#39;, &#39;loveless&#39;, &#39;sleepless&#39; ]
</code></pre>

From here, you can analyze the output and do the replacements yourself:

<pre><code class='language-python' lang='python'>dresses_data[&#39;SleeveLength&#39;].replace(&#39;sleevless&#39;, &#39;sleeveless&#39;, inplace = True)
</code></pre>

### What's the Benefit?

This is where you ask "What's the difference if it doesn't automatically fix my data?"

When you have large datasets, it can be hard to individually identify which items are misspelled. Using this method will allow you to have a list of all the items that are misspelled which can let you deal with it in a systematic way.