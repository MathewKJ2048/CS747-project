## Core vision



## List of functionalities

The goal of this project is to prove properties about a databse cluster. The databse is characterized by:

- Brokers - processes which store messages as they come in
- Receivers - which act on the messgae after getting a lease on them from a broker
- Messages - stored by brokers and leased to receivers, which act on the message

The messages are stored in waitlists for each cluster in the database. These waitlists are queried by sequencers which query every cluster.

## Detailed description

```
INVARIANTS 
    \* OneTenantOneCluster
    \* DeadLetterQueuesEmpty
    \* LeaseCannotBeRetaken
    \* MessageProcessedByOneReceiverAtATime

PROPERTIES 
    NoLostMsgs
    SentMsgsEventuallyReceived
    SentMsgsEventuallyDeleted
    QueuesEventuallyEmpty
    AllMsgsSent
    MessagesSent
    MessagesEnqueued
    MessagesReceived 
```

## Roadmap

- Literature review

- Creating a framework for finite state automata in Rocq, or familiarizing oneself with a suitable library for such a framework.

- Implementing states, transitions, actions, variables, guards and concurrency

- Proving simple results for small automata

[end of february]

- Describing the states and transitions used for the database, via translation from an existing implementation in TLA+

[mid march]

- Making strong assumptions about the correctness of the model to prove properties of the system

[end of march]

- Progressively weakening the assumptions about correctness while ensuring that the properties remain provable

[mid april]