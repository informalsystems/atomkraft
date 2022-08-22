# Atomkraft Installation Instructions

## Tool installation

There is one major prerequisite for using Atomkraft: [Python](https://www.python.org) 3.10. Please consult the [installation instructions](https://realpython.com/installing-python/) for your OS, in case you don't have it installed already.

When you have Python 3.10 installed, installing Atomkraft should be as easy as `pip install atomkraft`.

That's it! Please verify that the tools works by issuing `atomkraft` on the command line. You should see smth. like this:

![Atomkraft CLI](docs/images/cli.png)

## Blockchain binary

If you are interested in Atomkraft, you probably want to test some Cosmos SDK blockchain; so, there is a high probability you have a blockchain binary in your system already. If this is the case, feel free skip the rest of this section.

In case you don't have any Cosmos SDK blockchain binary locally, it should be easy to obtain it. The simplest solution if you want just to play with the tool is probably to use [Cosmos Hub (Gaia)](https://github.com/cosmos/gaia). You may either:

- download a precompiled binary for you system from [Gaia releases](https://github.com/cosmos/gaia/releases), or
- compile the blockchain binary locally
  ```sh
  git clone --depth 1 --branch v7.0.3 https://github.com/cosmos/gaia.git
  (cd gaia; make build)
  ```
  The blockchain binary will be at `./gaia/build/gaiad`.

## Java

This is not required for basic tool usage, e.g. for running standalone test scenarios against a blockchain. For advanced usage, we employ our in-house [Apalache Model Checker](https://apalache.informal.systems); it allows to generate test scenarios from TLA+ models. If you are interested in this functionality, please continue reading.

Atomkraft allows you to download and manage Apalache releases automatically, so you don't need to worry about that. The only prerequisite for using Apalache via Atomkraft is to have Java installed on your system. We recommend version 17 builds of OpenJDK, for example [Eclipse Temurin](https://adoptium.net/) or [Zulu](https://www.azul.com/downloads/?version=java-17-lts&package=jdk#download-openjdk). In case you don't have Java installed already, please download and install the package suitable for your system.
