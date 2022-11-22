# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Init", value \|-> [ wallets \|-> {"Alice", "Bob"} ] ]`|
|`balances`|`SetAsFun({<<"Alice", 100>>, <<"Bob", 100>>})`|
|`step`|`0`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Transfer", value \|-> [ amount \|-> 100, receiver \|-> "Bob", sender \|-> "Alice" ] ]`|
|`balances`|`SetAsFun({<<"Alice", 0>>, <<"Bob", 200>>})`|
|`step`|`1`|


</details>

