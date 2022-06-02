themes="@konodyuk/theme-ayu-mirage @arbennett/base16-nord @arbennett/base16-solarized-light @arbennett/base16-solarized-dark @arbennett/base16-monokai " 
keyBindings="@axlair/jupyterlab_vim "
##keyBindings="@ryantam626/jupyterlab_sublime " 
spellChecker="@ijmbarr/jupyterlab_spellchecker "
latex="@jupyterlab/latex "
headings="@aquirdturtle/collapsible_headings "
#tabNine="@tabnine/jupyterlab " # not clear if it supports latest version of JL
# executeTime="jupyterlab-execute-time " # not clear if it supports latest version of JL
# activeTab="jupyterlab-active-as-tab-name " # not clear if it supports latest version of JL
spreadsheet="jupyterlab-spreadsheet "
#ihaskell="jupyterlab-ihaskell"
extensions="${themes}${keyBindings}${spellChecker}${headings}${latex}${spreadsheet}"
#extensions="${themes}${keyBindings}${spellChecker}${headings}${latex}${spreadsheet}${ihaskell}"
#extensions="${themes}${headings}${spreadsheet}${keyBindings}${spellChecker}${latex}${ihaskell}"
#extensions="${activeTab}${themes}${headings}${spreadsheet}${executeTime}${tabNine}${keyBindings}${spellChecker}${latex}${ihaskell}"
generate-directory ${extensions} 
# jupyterlab-vim -> https://github.com/jwkvam/jupyterlab-vim/archive/refs/tags/v0.11.0.tar.gz
# jupyterlab-spellchecker -> https://github.com/jupyterlab-contrib/spellchecker/archive/refs/tags/v0.7.2.tar.gz
# jupyterlab-execute-time
# @krassowski/jupyterlab_go_to_definition
# @jupyterlab/csvviewer
# @jupyterlab/toc
# @jupyterlab/terminal
# @jupyterlab/pdf-extension
# jupyterlab-jupytext
# @jupyterlab/extensionmanager
# @jupyterlab/latex
# @ryantam626/jupyterlab_sublime
# @deathbeds/jupyterlab-font-anonymous-pro
# @deathbeds/jupyterlab-font-dejavu-sans-mono
# @tabnine/jupyterlab
# jupyterlab-active-as-tab-name 
