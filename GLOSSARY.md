# Netlib glossary

Use these technical terms with the meanings below. Use the same term for the same
concept in code comments and documentation.

## Network terms

**Network**:
A collection of nodes and directed links that permit steps for a traffic class.

**Node**:
One device in a network model.

**Link**:
A permitted directed step between two nodes for a traffic class.

**Traffic class**:
A named set of traffic with the same permitted links.

**Path**:
A finite sequence of permitted steps. A path can have zero steps.

**Walk**:
A path represented as a sequence of nodes. A walk can visit a node more than once.

**Reachability**:
The existence of a path from a source to a target. Each node reaches itself through a path with zero steps.

**Isolation**:
The absence of every path between the specified source and target nodes.

**Gateway**:
A node in a set that a mediation requirement designates for a necessary visit.

**Gateway group**:
A named set of gateways. A visit to any member satisfies the group visit.

**Mediation**:
The property that every path between specified endpoints visits a designated gateway group. A visit at an endpoint counts.

**Bypass**:
A path that avoids every node in a designated gateway group.

**Cut certificate**:
A node set that contains the source, excludes the target, and permits no step out of the set.

**Forward-closed**:
A property of a node set. Every permitted step from that set ends in the same set.

**Cluster**:
Several physical nodes that represent one architecture component.

**Failover**:
A change from a primary device to a standby device after a fault.

**Availability**:
Reachability that an explicit requirement requires. Mediation alone does not establish availability.

**Fault model**:
The admitted combinations of failed nodes and links for a stated guarantee.

**Domain contract**:
An abstract forwarding relation that a domain and its border transitions must preserve.


## Requirements and logic

**Selector**:
A description of a node set, by node ID, zone, role, or group.

**Selection**:
The node set that a selector denotes in a configuration or interpretation.

**Requirement**:
A source sentence and its formal obligation about network behavior.

**Requirement policy**:
A list of requirements that must all hold.

**Security goal**:
An explicit property that requirements should imply.

**Formula**:
A proposition built from atoms and Boolean connectives.

**Atom**:
A proposition that a formula treats as one indivisible item.

**Observation**:
A network proposition about reachability, isolation, or mediation.

**Valuation**:
An assignment of a Boolean value to each atom.

**Network model**:
A mathematical representation of network nodes and permitted steps.

**Propositional model**:
An assignment that satisfies the specified formulas.

**Semantics**:
The precise mathematical meaning of a formula or network object.

**Consistency**:
The existence of an assignment that satisfies every requirement.

**Entailment**:
A relation in which every model of the premises satisfies the conclusion.

**Countermodel**:
An assignment that satisfies the premises and makes the goal false. It need not describe a realizable network.

**Counterexample**:
A path, assignment, or other object that disproves a claim.

**Search node**:
One branch or constant-result step in propositional search.

**Search budget**:
The maximum number of search nodes for one solver query. Both branches share its remaining nodes.

**Impossibility proof**:
A proof that no valuation satisfies a specified formula or policy.

**Redundancy**:
A property of a requirement whose removal preserves all policy models.

**Completion**:
Additional supplied goals that make the policy imply the explicit goals without a contradiction.

**Domain law**:
A formula that connects observations and has a proof from the network semantics.


## Proof and implementation terms

**Abstraction**:
A reviewed relation between physical devices and architecture concepts. One concept can represent several devices.

**Refinement**:
A relation that represents concrete network steps in an abstract architecture.

**Stuttering refinement**:
A refinement that permits concrete steps within one abstract node and preserves gateway visits.

**Certificate**:
Data that a validator can use to establish a proposition.

**Certified value**:
A Boolean value with a Lean proof that connects the value to its proposition.

**Transition trace**:
A finite sequence of labeled state changes permitted by a transition relation.

**Trace refinement**:
A projection that represents each concrete transition by a finite abstract trace.

**Update plan**:
A command sequence with a proof that every intermediate snapshot satisfies its contract.

**Trust boundary**:
The division between formal guarantees and facts that need tests or review.


## Packet policies and routing

**Header**:
The source address, destination address, protocol number, and port numbers that identify a modeled packet.

**Five-tuple**:
The source address, destination address, protocol number, source port, and destination port considered together.

**Header rewrite**:
An explicit overwrite of selected modeled packet fields.

**Transfer state**:
A device location together with the complete current modeled header.

**NAPT**:
Network address and port translation between inside and public endpoints.

**Flow grant**:
A timed authorization record for one outbound five-tuple and its exact reverse reply.

**Mapping**:
A timed association between an inside endpoint/protocol pair and a public endpoint/protocol pair.

**Packet freshness**:
Evidence that a received packet belongs to the intended current communication instance.

**Processor**:
A packet stage that returns an updated store and either an output header or a drop.

**Store**:
The complete explicit state shared by successive calls to a packet processor.

**State replication**:
Transfer of state between devices so that another device can continue the modeled behavior.

**Conntrack record**:
A reported connection-tracking entry with original and reply tuples and supplied metadata.

**Direction key**:
An effective conntrack zone together with the complete input five-tuple for one direction.

**Tuple projection**:
The frozen association between an entry's input header and its direction-specific output header.

**Confirmed record**:
An ordinary connection record installed after the modeled final confirmation step.

**Fresh attachment**:
A new packet association created after a tuple lookup miss, before confirmation.

**Seen reply**:
A tracking flag set after the tracker accepts a reply, before later filter decisions.

**Context refinement**:
Permission inclusion for every declared packet header and connection-state label at a fixed processing position.

**Prefix**:
An address block defined by a base address and the number of shared initial bits.

**Packet match**:
A set of field conditions that select packet headers.

**Packet cell**:
A set of headers with the same decisions for every selected ACL and route predicate.

**Packet representative**:
One header used to check a complete packet cell under proved decision equality.

**FIFO queue**:
A queue that serves packets in their arrival order. FIFO means first in, first out.

**Backlog**:
The number of packets pending in the modeled queue.

**Service capacity**:
The maximum number of packets that a modeled queue tick can serve.

**Access control list**:
An ordered list of packet matches and permit or deny actions. The first matching rule supplies the action.

**Default action**:
The action for a packet that matches no rule.

**Shadowed rule**:
A rule whose removal preserves policy behavior because an earlier rule covers its match.

**Route**:
A destination prefix and its next hop or drop action.

**Longest-prefix selection**:
Route selection by the greatest matching prefix length. Equal lengths preserve the first route.

## Request enforcement

**Principal**:
A modeled identity that makes a request.

**Resource**:
The object that a request concerns.

**Operation**:
The action that a principal requests on a resource, such as read or write.

**Request**:
A principal, a resource, and an operation considered together.

**Authentication result**:
A supplied Boolean result that states whether the principal passes the identity check.

**Authorization result**:
A supplied Boolean result that states whether the request passes the permission check.

**Request policy**:
The authentication and authorization functions that determine request admission.

**Admitted request**:
A request whose authentication and authorization results are both true.

**Policy enforcement point**:
A gateway that permits entry or exit only when both request checks pass.

## Standards and evidence

**Source record**:
The document name, version, clause ID, and URL that identify a requirement's origin.

**Clause**:
An identified part of a source document.

**Applicability**:
The conditions under which a requirement concerns the selected model.

**Profile**:
A named set of selected requirements with explicit scope and assumptions.

**Evidence**:
An artifact or observation that supports a requirement result.

**Satisfied finding**:
A result whose selected model condition holds under its declared assumptions.

**Violated finding**:
A result whose selected model condition fails.

**Unsupported finding**:
A result for a property that the checker does not model.

**Missing-evidence finding**:
A result that lacks a necessary input or observation.

**Not-applicable finding**:
A result for a requirement outside the stated applicability conditions.

**Evidence completeness**:
The absence of unsupported and missing-evidence findings. It does not imply satisfaction.

## Wireless deployment

**Access point**:
A network device that supplies the modeled wireless access service.

**Basic service set**:
The station group that one access-point configuration serves. Its abbreviation is BSS.

**AP binding**:
A reviewed relation between an imported access-point interface and bridge and one modeled node.

**Protected management frame**:
A wireless management frame subject to the selected integrity and replay protections.

**RADIUS**:
The authentication service protocol between the modeled access point and its external authentication server.

## Session evidence

**Session**:
A context that records identity results, a current credential, a clock, and guarded admission.

**Credential**:
An issuer, subject, audience, scope list, expiration time, and supplied integrity result.

**Access token**:
A credential that an NF service producer checks before service admission.

**Network function**:
A modeled 5G service consumer, service producer, or authorization server. Its abbreviation is NF.

**Scope**:
The resource and operation that a credential permits.

**Admission safety**:
The property that every observed admitted request satisfies the selected current guards.

**Token reuse**:
Use of the same valid token for more than one request.

**Local revocation**:
Removal of the current session credential. This model operation does not maintain a persistent token blacklist.
