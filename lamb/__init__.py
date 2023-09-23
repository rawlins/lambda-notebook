__all__ = ['utils', 'types', 'meta', 'lang', 'tree_mini', 'parsing', 'magics',
           'lnsetup', 'display', 'combinators', 'auto']

__version_info__ = (0, 7, 0)
__release__ = False
__version__ = ".".join(str(i) for i in __version_info__)
if not __release__:
    __version__ = __version__ + "a1"
