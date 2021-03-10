# LICENCE
MiniLogo.hs, Render.hs and most of hw5.hs were written by [Eric Walkingshaw](https://github.com/walkie)

The buildBlock, buildProg, amazing function in hw6, as well as plateToLines.py and removeDecimals.sh is written by [Nathan Shaaban](https://github.com/ctrlaltf24) Licenced under MIT

[Kavo font](https://www.fontspace.com/kavo-font-f46946) (encoded in the letters and letters_clean folders, as well as the letters array in hw6) is only for personal use, see [https://www.fontspace.com/kavo-font-f46946](here) for more details.

# Procedure
- Downloaded the [Kavo font](https://www.fontspace.com/kavo-font-f46946)
- Converted each letter to a plate using FontForge's export feature for each letter individually
- [Used Bash and Sed](removeDecimals.sh) to force to ints
- [Used a python script](plateToLines.py) to parse the plate into a MiniLogo Block
- Appended into Haskell for your enjoyment
# Letters Included
A through Z as well as space tab and newline are added