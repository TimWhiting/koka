import Koka.Common.Name

open Koka.Common.Name

-- Test pathToModuleName
#guard pathToModuleName "foo/bar/baz" == newModuleName "foo/bar/baz"
#guard pathToModuleName "\\windows\\path\\" == newModuleName "windows/path"

-- Test readQualifiedName
#guard (readQualifiedName "std/core/True").module == "std/core"
#guard (readQualifiedName "std/core/True").stem == "True"

-- Test implicit param name
#guard isImplicitParamName (toImplicitParamName (newName "test"))

-- Inverse operations
#guard fromImplicitParamName (toImplicitParamName (newName "test")) == newName "test"
#guard fromHandlerName (toHandlerName (newName "test")) == newName "test"
#guard fromOperationsName (toOperationsName (newName "test")) == newName "test"
#guard unmakeHidden "expr" (makeHiddenName "expr" (newName "test")) == newName "test"
#guard fromValueOperationsName (toValueOperationName (newName "test")) == newName "test"
#guard pathToModuleName "foo__bar" == newModuleName "foo_bar"
#guard pathToModuleName "foo_dash_bar" == newModuleName "foo-bar"

#eval showBinary 4 5
#eval showBinary 8 0
#eval showHexFloat 1.0
#eval showHexFloat 0.0
#eval showHexFloat (-0.5)
#eval showHexFloat (0.0 / 0.0)
#eval showHexFloat (1.0 / 0.0)
