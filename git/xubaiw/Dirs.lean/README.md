# Dirs.lean

Retrieve platform-specific directories in Lean 4, ported from Rust's [`dirs`](https://github.com/dirs-dev/dirs-rs).

Currently, only Linux and MacOS is supported:

| Function name | Value on Linux |  Value on macOS |
| ------------- | -------------- | --------------- |
| `home` | `some $HOME` | `some $HOME` |
| `cache` | `some $XDG_CACHE_HOME <⎮> some $HOME/".cache"` | `some $HOME/"Library"/"Caches"` |
| `config` | `some $XDG_CONFIG_HOME <⎮> some $HOME/".config"` | `some $HOME/"Library"/"Application Support"` |
| `data` | `some $XDG_DATA_HOME <⎮> some $HOME/".local"/"share"` | `some $HOME/"Library"/"Application Support"` |
| `dataLocal` | `some $XDG_DATA_HOME <⎮> some $HOME/".local"/"share"` | `some $HOME/"Library"/"Application Support"` |
| `executable` | `some $XDG_BIN_HOME <⎮> some $HOME/".local"/"bin"` | `none` |
| `preference` | `some $XDG_CONFIG_HOME <⎮> some $HOME/".config"` |  `some $HOME/"Library"/"Preferences"` |
| `runtime` | `some $XDG_RUNTIME_DIR <⎮> none` | `none` |
| `state` | `some $XDG_STATE_HOME <⎮> some $HOME/".local"/"state"` | `none` |
| `audio` | `some XDG_MUSIC_DIR <⎮> none` | `some $HOME/"Music"` |
| `desktop` | `some XDG_DESKTOP_DIR <⎮> none` | `some $HOME/"Desktop"` |
| `document` | `some XDG_DOCUMENTS_DIR <⎮> none` | `some $HOME/"Documents"` |
| `download` | `some XDG_DOWNLOAD_DIR <⎮> none` | `some $HOME/"Downloads"` |
| `font` | `some $XDG_DATA_HOME/"fonts" <⎮> some $HOME/".local"/"share"/"fonts"` | `some $HOME/"Library"/"Fonts"` |
| `picture` | `some XDG_PICTURES_DIR <⎮> none` | `some $HOME/"Pictures"` |
| `public` | `some XDG_PUBLICSHARE_DIR <⎮> none` | `some $HOME/"Public"` |
| `template` | `some XDG_TEMPLATES_DIR <⎮> none` | `none` |
| `video` | `some XDG_VIDEOS_DIR <⎮> none` | `some $HOME/"Movies"` |
