import VersoSlides
import LeanOA.ICERM.Loreaux

open VersoSlides

def main : IO UInt32 :=
  slidesMain
    (config :=
      { theme := "black",
        slideNumber := true,
        width := 1920,
        height := 1080,
        transition := "slide" })
    (doc := %doc LeanOA.ICERM.Loreaux)
