import os
import logging

LOG_DIRECTORY = os.path.dirname(os.path.realpath(__file__))
logging.basicConfig(filename = os.path.join(LOG_DIRECTORY , "log") , 
                    filemode = "w" , 
                    format='%(message)s   # [%(levelname)s|%(funcName)s|%(filename)s|%(lineno)d]')
logger = logging.getLogger()
logger.setLevel(logging.DEBUG)

