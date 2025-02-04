import os.path

from broker import broker


class simpleStubBroker(broker):
    """
    Broker that automatically gathers stub files by search for file name
    corresponding to module name in a list of directories
    """

    def stub_file_for_module(self, module):
        """"""
        for broker_dir in self.get_broker_dirs():
            fname = os.path.join(broker_dir, module + '.c')
            if os.path.exists(fname):
                return fname
        return ''

    def get_broker_dirs(self):
        """
        Return the list of directories to inspect
        """
        return []
