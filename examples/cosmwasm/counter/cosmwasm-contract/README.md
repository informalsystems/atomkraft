# counter-example-contract

This smart contract implements simple counting.

# Messages

Message format is JSON. Exact format can be seen from json schema files under _schema_ directory.

## Instantiate

**Params:** count - initial counter value.

**Description:** Sets initial counter value. Sender is also saved. Sender address is gather from the environment and saved as owner.

## Increment

**Params:** None

**Description:** Increments counter value.

## Reset

**Params:** count - new counter value.

**Description:** Resets counter value to the new value. If sender is not an owner, method returs exception.

## GetCount

**Params:** None

**Descrpiton:** Query for counter current value.

**Returns:** Current current value.
