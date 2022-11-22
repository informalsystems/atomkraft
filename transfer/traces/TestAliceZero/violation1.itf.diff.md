# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.wallets`|`{"Alice", "Bob"}`|`None`|
|`action.tag`|`Init`|`Transfer`|
|`action.value.amount`|`None`|`100`|
|`action.value.receiver`|`None`|`"Bob"`|
|`action.value.sender`|`None`|`"Alice"`|

</details>
<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Alice")`|`100`|`0`|
|`balances("Bob")`|`100`|`200`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`0`|`1`|

</details>

</details>

