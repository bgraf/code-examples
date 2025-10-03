import unittest
from model_1st import *


class TestCreateOrder(unittest.TestCase):
    def test_creates_order(self):
        order_no = "ord#1"

        s = State()
        create_order(s, id=order_no, production_date=date(2025, 12, 1))

        order = s.orders.get(order_no)
        self.assertIsNotNone(order)
        self.assertFalse(order.is_scheduled())

    def test_cannot_create_order_twice(self):
        order_no = "ord#1"

        s = State()
        create_order(s, id=order_no, production_date=date(2025, 12, 1))

        with self.assertRaises(PreconditionError):
            create_order(s, id=order_no, production_date=date(2025, 12, 1))


class TestExternalService(unittest.TestCase):
    def test_external_processing(self):
        order_no = "ord#1"
        s = State()

        create_order(s, id=order_no, production_date=date(2025, 12, 1))
        external_service_process_request(s)
        process_response(s)

        order = s.orders.get(order_no)
        self.assertTrue(order.is_scheduled())
        self.assertGreaterEqual(order.delivery_date, order.production_date)

    def test_external_with_order_change(self):
        order_no = "ord#1"
        s = State()

        create_order(s, id=order_no, production_date=date(2025, 11, 1))
        external_service_process_request(s)
        process_response(s)
        
        change_order(s, id=order_no, new_production_date=date(2025, 12, 1))

        # Order is unscheduled after change
        order = s.orders.get(order_no)
        self.assertFalse(order.is_scheduled())

        external_service_process_request(s)
        process_response(s)

        # Order is scheduled after processing
        order = s.orders.get(order_no)
        self.assertTrue(order.is_scheduled())
        self.assertGreaterEqual(order.delivery_date, order.production_date)

    def test_external_with_order_change_and_delayed_processing(self):
        order_no = "ord#1"
        s = State()

        create_order(s, id=order_no, production_date=date(2025, 11, 1))
        # No processing happening.. slow external service
        change_order(s, id=order_no, new_production_date=date(2025, 12, 1))

        # Order is unscheduled after change
        order = s.orders.get(order_no)
        self.assertFalse(order.is_scheduled())

        external_service_process_request(s)
        process_response(s)

        # Order is scheduled after processing
        order = s.orders.get(order_no)
        if order.is_scheduled():
            self.assertGreaterEqual(order.delivery_date, order.production_date)

if __name__ == '__main__':
    unittest.main()
