---------------------------- MODULE model_err ----------------------------
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

Request(o, d) == 
  queueToService' = Append(queueToService, [
    order |-> o,
    prod |-> d
  ])

CreateOrder(o) == 
    /\ ~IsCreatedOrder(o)
    /\ \E nextDate \in Dates:
        /\ localOrders' = [ localOrders EXCEPT  
                            ![o].version = @ + 1, 
                            ![o].productionDate = nextDate
                          ]
        /\ Request(o, nextDate)
    /\ UNCHANGED << queueToLocal >>

UpdateOrder(o) ==
    /\ localOrders[o].version <= 2
    /\ IsCreatedOrder(o)
    /\ \E nextDate \in Dates:
        /\ localOrders[o].productionDate /= nextDate
        /\ localOrders' = [ localOrders EXCEPT  
                            ![o].version = @ + 1, 
                            ![o].productionDate = nextDate,
                            ![o].deliveryDate = 0
                          ]
        /\ Request(o, nextDate)
    /\ UNCHANGED << queueToLocal >>

ExternalServiceProcessRequest ==
  /\ Len(queueToService) > 0
  /\ LET req == Head(queueToService) 
     IN 
        queueToLocal' = Append(queueToLocal, [
          order |-> req.order,
          delivery |-> req.prod + 1
        ])
  /\ queueToService' = Tail(queueToService)
  /\ UNCHANGED << localOrders >>

LocalServiceProcessResponse ==
  /\ Len(queueToLocal) > 0
  /\ LET resp == Head(queueToLocal) 
      IN
      localOrders' = [ localOrders EXCEPT ![resp.order].deliveryDate = resp.delivery ]
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
