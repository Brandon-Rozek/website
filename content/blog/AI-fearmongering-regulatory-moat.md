---
title: "AI fearmongering for regulatory moats"
date: 2023-05-28T19:45:55-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

On May 16th 2023, Sam Altman [testified before a congress subcommittee](https://www.washingtonpost.com/technology/2023/05/16/ai-congressional-hearing-chatgpt-sam-altman/) on the need for AI regulation. During so, he proposes three actions:

1. Form a new government agency charged with licensing large AI models, and allow it to revoke it for companies whose don’t comply.
2. Create a set of safety standards for AI models.
3. Require independent audits, by independent experts.

Okay I can get behind the idea behind "safety standards" but what about this new government agency? Why would Sam Altman the CEO of OpenAI want the creation of a new government agency? 

Some (including me) speculate that he's trying to create a *regulatory moat* for OpenAI. 

We can see where this goes. There are thousands of AI startups trying to sell models of various kinds, the idea is that they all need to register and be regularly monitored by a government agency? 

This would probably lead to long wait times for these AI licenses with a few companies holding the majority of the licenses. Startups funded through Y-combinator rarely go beyond [two years](https://ycuniverse.com/longevity-of-yc-startups-from-funding-through-acquisition/). 

It's a great way of trying to stamp out competition really. Currently it's highly expensive to train one of these large language models (LLMs) but would that always be the case? In the inevitable future where other companies have the compute to generate one of these models, OpenAI needs to find a way to keep its market share.

Now you might think I'm being to pessimistic. What if Sam Altman is trying to think about the best for society? If that's the case, then I don't think he would threaten to not [provide AI services in the EU](https://www.reuters.com/technology/openai-may-leave-eu-if-regulations-bite-ceo-2023-05-24/) due to their stringent regulations.

He's walked back the comment since then, but let's take a brief look at what the EU regulations look like. 

- Most current version I'm aware of: https://digital-strategy.ec.europa.eu/en/policies/regulatory-framework-ai]
- Summary in Presentation Form: https://www.ceps.eu/wp-content/uploads/2021/04/AI-Presentation-CEPS-Webinar-L.-Sioli-23.4.21.pdf

Generative models are considered at the time of writing to be a "high-risk" AI model. The additional regulations the EU imposes on these companies are:

>- adequate risk assessment and mitigation systems;
>- high quality of the datasets feeding the system to minimise risks and discriminatory outcomes;
>- logging of activity to ensure traceability of results;
>- detailed documentation providing all information necessary on the system and its purpose for authorities to assess its compliance;
>- clear and adequate information to the user;
>- appropriate human oversight measures to minimise risk;
>- high level of robustness, security and accuracy.

I feel like most of those bullet points fall under Altman's "safety standards for AI models". Though I think what he really has an issue with is the data privacy requirements set forth by the EU. In fact this is an often criticized part of these models trained on Internet data:

- Personally identifiable information
- Copyright information
- Conspiracy/Misinformation
- etc.

My personal opinion is that these models should not be trained on the above data, but this isn't a new discussion. More recently, the issue of copyright has been brought up with generative code products such as GitHub Copilot. I am interested to see how it makes its way through the US court systems here.

Another question I think we need to answer as a society is whether to hold companies accountable for defamation. There are already instances where [ChatGPT incorrectly accused a law professor of sexual harrasment](https://www.washingtonpost.com/technology/2023/04/05/chatgpt-lies/). With the push to [replace search](https://www.nytimes.com/2022/12/21/technology/ai-chatgpt-google-search.html) with these automatically generated responses, we can see how misinformation may be propagated and then further reinforced by these models.

I don't want to say that it's a bad idea for congress to regulate AI. I'm mostly suggesting that perhaps we shouldn't call upon people who hold direct financial interest to come up with the regulations that will apply to themselves. That might lead these actors to bring attention to certain issue while avoiding others...

