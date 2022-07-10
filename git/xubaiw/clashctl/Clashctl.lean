import Lean.Data.Json
import Std.Data.HashMap
import Socket

open Socket Lean Std

/-!
## Convenience methods for manipulating response string
-/
abbrev Response := String

namespace Response

variable (r : Response)

def text? : Option String := r.splitOn "\r\n\r\n" |>.get? 1

def json? : Except String Json := 
  match r.text? with
  | some t => Json.parse t
  | _ => .error "text is empty"

def status? : Option String :=
  if let some l := r.splitOn "\r\n" |>.head? then
    l.splitOn " " |>.get? 1
  else
    none

end Response

/-!
## HTTP
-/
def get (host port path : String) : IO Response := do 
  -- connect
  let remoteAddr ← SockAddr.mk host port .inet .stream
  let s ← Socket.mk .inet .stream
  s.connect remoteAddr
  -- send
  let strSend := 
    s!"GET {path} HTTP/1.0\r\n" ++
    s!"Host: {host}\r\n" ++
    "\r\n\r\n"
  discard <| s.send strSend.toUTF8
  -- receive
  let r : Response ← String.fromUTF8Unchecked <$> s.recv 5000
  s.close
  return r

def putJson (host port path : String) (json : Json) : IO Response := do 
  -- connect
  let remoteAddr ← SockAddr.mk host port .inet .stream
  let s ← Socket.mk .inet .stream
  s.connect remoteAddr
  -- send
  let body := toString json
  let strSend := 
    s!"PUT {path} HTTP/1.0\r\n" ++
    s!"Host: {host}\r\n" ++
    "Content-Type: application/json\r\n" ++
    s!"Content-Length: {body.utf8ByteSize}" ++
    "\r\n\r\n" ++
    body
  discard <| s.send strSend.toUTF8
  -- receive
  let r : Response ← String.fromUTF8Unchecked <$> s.recv 5000
  s.close
  return r

/-!
## Data Structure for proxy
-/
structure Proxy where
  history : Array String
  name : String
  type : String
  udp : Bool
  all : Option $ Array String
  now : Option String
  deriving Lean.FromJson, Repr

def getProxies : IO $ Array String := do
  let r ← get "127.0.0.1" "9090" "/proxies/SelectGroup"
  match r.json? with
  | .ok j =>
    match j.getObjValAs? (Array String) "all" with
    | .ok all => return all
    | .error e => throw <| IO.Error.userError s!"fail to get `all` field. {e}"
  | .error e => throw <| IO.Error.userError s!"fail to parse response json. {e}"

def getProxy : IO String := do
  let r ← get "127.0.0.1" "9090" "/proxies/SelectGroup"
  match r.json? with
  | .ok j =>
    match j.getObjValAs? String "now" with
    | .ok now => return now
    | .error e => throw <| IO.Error.userError s!"fail to get `now` field. {e}"
  | .error e => throw <| IO.Error.userError s!"fail to parse response json. {e}"

def getDelay (name url : String) (timeout : Nat) : IO $ Option Nat := do
  let path := s!"/proxies/{name}/delay?timeout={timeout}&url={url}"
  let r ← get "127.0.0.1" "9090" path
  match r.json? with
  | .ok j =>
    match j.getObjValAs? Nat "delay" with
    | .ok delay => return delay
    | _ => return none
  | .error e => throw <| IO.Error.userError s!"fail to parse response json. {e}"

def getDelays (url : String) (timeout : Nat) : IO $ HashMap String $ Option Nat:= do
  let proxies ← getProxies
  proxies.foldlM (λ acc x => (getDelay x url timeout).map (acc.insert x ·)) HashMap.empty

structure ProxySetting where
  name : String
  deriving ToJson

def setProxy (name : String) : IO Bool := do
  let j := ToJson.toJson <| ProxySetting.mk name
  let r ← putJson "127.0.0.1" "9090" "/proxies/SelectGroup" j
  return r.status? == some "204"
