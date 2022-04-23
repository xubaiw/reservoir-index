import Mrs

def main (hellos : List String)  : IO Unit :=
  for hello in hellos do
    IO.println s!"Hello, {hello}!"

#eval main ["Alexandre"]

