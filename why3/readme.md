 Add the following to `why3-0.86.3/share/provers-detection-data.conf`:
 
 ```
  [ATP polya]
  name = "Polya"
  exec = "polya"
  version_switch = "-version f"
  version_regexp = "\\([^ \n\r]+\\)"
  version_ok = "0.1"
  driver = "drivers/polya.drv"
  command = "%l/why3-cpulimit %t %m -s %e -z %f"
```

Save `polya.drv` to `why3-0.86.3/drivers`.

Recompile why3 and detect provers.