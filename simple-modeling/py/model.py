from typing import Dict, List, Optional
from dataclasses import dataclass, field
from datetime import date, timedelta


class PreconditionError(Exception):
    def __init__(self, msg):
        super().__init__(msg)


@dataclass
class Order:
    production_date: date
    delivery_date: Optional[date] = None
    version: int = 0

    def is_scheduled(self):
        return self.delivery_date is not None


@dataclass
class Request:
    order_id: str
    version: int
    production_date: date


@dataclass
class Response:
    order_id: str
    version: int
    delivery_date: date


@dataclass
class State:
    orders: Dict[str, Order] = field(default_factory=dict)
    queue_to_external: List[Request] = field(default_factory=list)
    queue_from_external: List[Response] = field(default_factory=list)


def create_order(state: State, *, id: str, production_date: date):
    id = id.strip()
    assert len(id) > 0, "empty order id is not permitted"

    if id in state.orders:
        raise PreconditionError(f'order {id} already exists')

    order = Order(production_date=production_date)
    state.orders[id] = order
    state.queue_to_external.append(
        Request(order_id=id, version=order.version, production_date=production_date))


def change_order(state: State, *, id: str, new_production_date: date):
    if id not in state.orders:
        raise PreconditionError(f'order {id} does not exist')

    order = state.orders[id]
    order.production_date = new_production_date
    order.delivery_date = None
    order.version += 1
    state.queue_to_external.append(
        Request(order_id=id, version=order.version, production_date=new_production_date))


def external_service_process_request(state: State):
    if len(state.queue_to_external) == 0:
        raise PreconditionError('empty queue')

    req = state.queue_to_external.pop(0)

    state.queue_from_external.append(Response(
        order_id=req.order_id,
        version=req.version,
        delivery_date=req.production_date + timedelta(weeks=1),
    ))


def process_response(state: State):
    if len(state.queue_from_external) == 0:
        raise PreconditionError('empty queue')

    resp = state.queue_from_external.pop(0)
    order = state.orders.get(resp.order_id)
    if order is None:
        raise ProgrammerError(f'order {resp.order_id} does not exist')

    if order.version == resp.version:
        order.delivery_date = resp.delivery_date
