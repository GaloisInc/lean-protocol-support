# lean-protocol-support
This repo contains various modules for lean.

The primary purpose is to help reason about network protocols, including communication between systems,
serializing and deserializing messages, and some core cryptographic concepts.

Once Lean's standard library has matured, and our own contributions are more mature, we may migrate
code out of this into dedicated libraries.

Galois is unable to provide support for this library.  For questions, contact Joe Hendrix <jhendrix@galois.com>.


A brief summary of each module (that isn't obvious from its name) follows

* __crypto__: executable Implementations of HMAC and SHA2
  * __merkle__: Merkle trees, get paths through a merkle tree where the leafs are defined by a list
* __csp__: A definition of communicating sequential processes
* __data__: A few data libraries
  * __binary__: A binary tree with internal nodes
  * __bounded_list__: A list parameterized by a nat and a proof that length is less than that nat
  * __lp_tree__: A convenient datastructure for converting lists into left perfect trees whose internal nodes are defined as combinations of the leafs
  * __tree_paths__: Paths through trees
  * __tree__: n-ary trees
* __network__: Specification and implementation of a network model
  * __network_monad__: A monad for reading and writing to sockets
  * __network_implementation__: An instance of network monad
  * __action__, __labels__: A syntax for representing the actions that can occur in a network
  * __agent_facts__, __network_local_abs__: Lemmas you can apply to an agent on an abitrary network
* __subset__: Defines subsets over types, and fixpoints over those subsets
* __temporal__: Linear temporal logic and proof rules for interactive proving using temporal logic
