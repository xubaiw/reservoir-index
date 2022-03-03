import BuildSystems.Store

structure Trace
  (k v r : Type _)
where
  key     : k
  depends : List (k × v)
  result  : r

structure VT
  (k v : Type _)
where
  traces: List (Trace k v (Hash v))

def VT.record
  (vt    : VT k v)
  (key   : k)
  (value : Hash v)
  (deps  : List (k × Hash v))
  : VT k v
:=
  VT.mk (Trace.mk key deps value :: vt.traces)

def VT.verify
  [BEq k]
  [BEq v]
  [Monad m]
  (vt    : VT k v)
  (key   : k)
  (value : Hash v)
  (fetch : (k → m (Hash v)))
  : m Bool
:=
  vt.traces.anyM fun trace => do
    if trace.key != key then false
    else if trace.result != value then false
    else trace.depends.allM fun (k, h) => do (← fetch k) == h

structure CT
  (k v : Type _)
where
  traces: List (Trace k v v)

def Store.isDirty
  [BEq k]
  [BEq v]
  [Hashable v]
  (store : Store (CT k v) k v)
  (key   : k)
  : Bool
:=
  !store.info.traces.any
    fun trace => trace.key == key
              && trace.result == store.getValue key
              && trace.depends.all fun (k, h) => store.getHash k == h

def CT.record
  (ct    : CT k v)
  (key   : k)
  (value : v)
  (deps  : List (k × Hash v))
  : CT k v
:=
  CT.mk (Trace.mk key deps value :: ct.traces)

def CT.construct
  [BEq k]
  [BEq v]
  [Monad m]
  (ct    : CT k v)
  (key   : k)
  (fetch : (k → m (Hash v)))
  : m (List v)
:= do
  List.join $ ← ct.traces.mapM fun trace => do
    if trace.key != key then []
    else
      let sameInputs ← trace.depends.allM fun (k, h) => do (← fetch k) == h
      if sameInputs then [trace.result] else []

structure DCT
  (k v : Type _)
where
  traces: List (Trace k v v)

def DCT.deepDependencies
  [BEq k]
  [Hashable v]
  : DCT k v
  → Hash v
  → k
  → List k
:= sorry

def DCT.record
  [BEq k]
  [Hashable v]
  [Monad m]
  : DCT k v
  → k
  → v
  → List k
  → (k → m (Hash v))
  → m (DCT k v)
:= sorry

def DCT.construct
  [BEq k]
  [Hashable v]
  [Monad m]
  : DCT k v
  → k
  → (k → m (Hash v))
  → m (List v)
:= sorry
