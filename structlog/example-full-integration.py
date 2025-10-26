import logging
import random
import structlog
import time

shared_processors = [
    structlog.stdlib.add_logger_name,
    structlog.stdlib.add_log_level,
    structlog.stdlib.PositionalArgumentsFormatter(),
    structlog.processors.TimeStamper(fmt="iso", utc=True),
    structlog.processors.StackInfoRenderer(),
    structlog.processors.format_exc_info,
    structlog.processors.UnicodeDecoder(),
]

structlog.configure(
    processors=shared_processors + [
        structlog.stdlib.ProcessorFormatter.wrap_for_formatter,
    ],
    logger_factory=structlog.stdlib.LoggerFactory(),
)

formatter = structlog.stdlib.ProcessorFormatter(
    foreign_pre_chain=shared_processors,
    processors=[
        structlog.processors.CallsiteParameterAdder(
            {
                structlog.processors.CallsiteParameter.FILENAME,
                structlog.processors.CallsiteParameter.FUNC_NAME,
                structlog.processors.CallsiteParameter.LINENO,
            }
        ),
        structlog.stdlib.ProcessorFormatter.remove_processors_meta,
        structlog.processors.EventRenamer('message'),
        structlog.processors.JSONRenderer(),
    ]
)

handler = logging.StreamHandler()
handler.setFormatter(formatter)

logging.basicConfig(
    handlers=[handler],
    level=logging.INFO,
)

import lib

def main():
    log = structlog.get_logger("main")

    log.info("howdy!")

    for i in range(10000):
        c = random.randrange(0, 4)
        match c:
            case 0:
                log.info("iteration", i=i)
            case 1:
                log.warning("something happend", i=i)
            case 2:
                log.error("error occured!", i=i)
            case 3:
                try:
                    1 / 0
                except:
                    log.exception("operation failed", i=i)

        time.sleep(1)


if __name__ == "__main__":
    main()
