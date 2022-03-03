
namespace LeanPlay

def usage := "

USAGE:
  lean-play [OPTIONS] <COMMAND>

OPTIONS:
  --version             print version and exit
  --help, -h            print help of the program or a command and exit
  --dir, -d=file        use the package configuration in a specific directory
  --file, -f=file       use a specific file for the package configuration

COMMANDS:"

def helpCmd : (cmd : String) → String
| _           => usage

def help : (cmd? : Option String) → String
| some cmd => helpCmd cmd
| none => usage
