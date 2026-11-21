module
public import I3_380.Engine.RegisterPorts
@[expose] public section

namespace PalomarI3380.Engine

def frame (path : List Bool) (gap : Nat) (rs : List Nat) : Configuration :=
  atRight Port.root [true] (path ++ (zeros gap ++ registers rs))

end PalomarI3380.Engine
