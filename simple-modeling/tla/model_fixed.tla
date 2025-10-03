---------------------------- MODULE model_fixed ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    ORDERS

VARIABLES
    localOrders,
    queueToService,
    queueToLocal

vars == << localOrders, queueToService, queueToLocal >>

Dates == 1..3

Init == 
  /\ localOrders = [ o \in ORDERS |-> 
      [
        version         |-> 0,
        productionDate  |-> 0,
        deliveryDate    |-> 0
      ]
    ]
  /\ queueToService = <<>>
  /\ queueToLocal = <<>>

IsCreatedOrder(o) == localOrders[o].version > 0
IsScheduledOrder(o) == localOrders[o].deliveryDate > 0

Request(o, d, v) == 
  queueToService' = Append(queueToService, [
    order |-> o,
    prod |-> d,
    version |-> v
  ])

CreateOrder(o) == 
    /\ ~IsCreatedOrder(o)
    /\ \E nextDate \in Dates:
        LET nextVersion == localOrders[o].version + 1
        IN
        /\ localOrders' = [ localOrders EXCEPT  
                            ![o].version = nextVersion, 
                            ![o].productionDate = nextDate
                          ]
        /\ Request(o, nextDate, nextVersion)
    /\ UNCHANGED << queueToLocal >>

UpdateOrder(o) ==
    /\ localOrders[o].version <= 2
    /\ IsCreatedOrder(o)
    /\ \E nextDate \in Dates:
        LET nextVersion == localOrders[o].version + 1
        IN
        /\ localOrders[o].productionDate /= nextDate
        /\ localOrders' = [ localOrders EXCEPT  
                            ![o].version = nextVersion, 
                            ![o].productionDate = nextDate,
                            ![o].deliveryDate = 0
                          ]
        /\ Request(o, nextDate, nextVersion)
    /\ UNCHANGED << queueToLocal >>

ExternalServiceProcessRequest ==
  /\ Len(queueToService) > 0
  /\ LET req == Head(queueToService) 
     IN 
        queueToLocal' = Append(queueToLocal, [
          order |-> req.order,
          delivery |-> req.prod + 1,
          version |-> req.version
        ])
  /\ queueToService' = Tail(queueToService)
  /\ UNCHANGED << localOrders >>

LocalServiceProcessResponse ==
  /\ Len(queueToLocal) > 0
  /\ LET resp == Head(queueToLocal) 
      IN
      IF resp.version = localOrders[resp.order].version
      THEN
        localOrders' = [ localOrders EXCEPT ![resp.order].deliveryDate = resp.delivery ]
      ELSE
        UNCHANGED << localOrders >>
  /\ queueToLocal' = Tail(queueToLocal)
  /\ UNCHANGED << queueToService >>
    
Next == 
  \/  \E o \in ORDERS:
      \/ CreateOrder(o)
      \/ UpdateOrder(o)
  \/ ExternalServiceProcessRequest
  \/ LocalServiceProcessResponse
  \/ /\ \A o \in ORDERS: 
          localOrders[o].version = 3
     /\ UNCHANGED vars
  

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ WF_vars(Next)

(* Invariants *)

DeliveryUnsetOrAfterProduction ==
  \A o \in ORDERS:
    \/ ~IsScheduledOrder(o)
    \/ localOrders[o].deliveryDate >= localOrders[o].productionDate

(* Property *)

GetsDeliveryDate == 
  \A o \in ORDERS:
    localOrders[o].deliveryDate = 0 ~> localOrders[o].deliveryDate > 0

============================================================================
