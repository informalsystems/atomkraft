# Atomkraft: E2E testing for Cosmos blockchains

The [Cosmos Network](https://cosmos.network) of [IBC](https://ibcprotocol.org)-connected blockchains is growing tremendously fast. There is one aspect though, which has been not yet fully addressed, namely quality assurance: how do we make sure that Cosmos-based blockchains are secure, and don't contain security issues that pose hazards for user funds?

`Atomkraft` is designed as an automated solution for easy generation and execution of massive end-to-end (E2E) test suites for Cosmos SDK based blockchains. When designing the tool we kept two main categories of users for it: security auditors, and Cosmos SDK developers. The list is of course non-exclusive, and the roles may intersect.

![Atomkraft users](docs/images/atomkraft-users.svg)
