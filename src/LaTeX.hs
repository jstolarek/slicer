{-# LANGUAGE ExistentialQuantification #-}

module LaTeX where

import System.Directory
import Control.Monad
import Text.PrettyPrint as PrettyPrint

import Util


-- Whether to generate LaTeX markup (for the fancyvrb package).
forLaTeX :: Bool
forLaTeX = True

forBeamer :: Bool
forBeamer = False

withOverlays :: Bool
withOverlays = False

testFolder :: FilePath
testFolder = "Test//"

reportAll :: String -> [Figure] -> IO ()
reportAll testName reports = 
   mapM_ (report testName) $ zip reports $ iterate (+1) 1

report :: String -> (Figure, Integer) -> IO ()
report testName (fig, n) =
   let suffix = "-" ++ show n in
   writeFigure n (testFile ++ suffix) fig (labelPrefix ++ suffix)

   where
      labelPrefix = "example-" ++ testName
      testFile = "fig-" ++ labelPrefix

      writeFigure :: Integer -> FilePath -> Figure -> String -> IO ()
      writeFigure n file fig label = do
         let tag = show $ figTag $ contents fig
         let overlayRoot = file ++ "-overlay"
         writeFile (testFolder ++ file ++ ".tex") $ 
            "\\begin{" ++ tag ++ "}\n" ++ 
            (if figType fig == ContinueFig then "\\ContinuedFloat\n" else "") ++
            (showContents overlayRoot $ contents fig) ++ "\n" ++
            "\\vspace{-8pt}\n" ++ captionTag ("[" ++ testName ++ "] " ++ caption fig) ++ 
            "\\label{fig:" ++ label ++ "}\n" ++
            "\\end{" ++ tag ++ "}\n"

captionTag :: String -> String
captionTag caption =
   if forBeamer then "" else "\\caption{" ++ caption ++ "}\n"

data Figure = Figure {
   figType :: FigType,
   caption :: String,
   contents :: FigContents
}

data FigType = ContinueFig | NewFig
   deriving Eq

data FigContents = 
   SingleFig FigText |
   DoubleFig FigText FigText |          -- side-by-side, shared caption
   SubFigs FigTag [(String, FigText)]   -- bunch of subfigs, individual captions (plus shared caption)

-- Convenient uniform view of fig contents.
subfigs :: FigContents -> [(Integer, FigText)]
subfigs (SingleFig text) = [(1, text)]
subfigs (DoubleFig text1 text2) = [(1, text1), (2, text2)]
subfigs (SubFigs _ texts) = zip (iterate (+1) 1) $ snd $ unzip texts

data FigTag = Fig | FigStar
   deriving Eq

instance Show FigTag where
   show Fig = "figure"
   show FigStar = if forBeamer then "figure" else "figure*"

-- Whether the figure contents require two columns or one.
figTag :: FigContents -> FigTag
figTag (SingleFig _) = Fig
figTag (DoubleFig _ _) = FigStar
figTag (SubFigs figTag _) = figTag

data FigText = 
   forall a . PP a => Pretty a |   
   Plain String

style_ :: Style
style_ = Style PageMode 115 1.5

showSubfig :: FilePath -> (Integer, FigText) -> String
showSubfig overlayRoot (n, text) = 
   (if withOverlays then inputFile (overlay overlayRoot n) else id) $ 
   verbatim $ case text of
      Plain str -> str
      Pretty a -> renderStyle style_ $ pp a

-- Prepend a LaTeX "input" of a file.
inputFile :: FilePath -> String -> String
inputFile file = 
   (("\\input{" ++ file ++ "}\n") ++)

-- An overlay root pathname, augmented with an index and file extension.
overlay :: FilePath -> Integer -> String
overlay overlayRoot n = 
   overlayRoot ++ "-" ++ show n ++ ".tex"

showContents :: FilePath -> FigContents -> String
showContents overlayRoot contents = 
   case contents of
      SingleFig _ -> 
         showSubfig overlayRoot $ (subfigs contents)!!0
      DoubleFig _ _ -> 
         columnise ((subfigs contents)!!0) False ++ 
         columnise ((subfigs contents)!!1) False
      SubFigs figTag texts -> 
         concatMap (subFloat $ figTag == Fig) $ zip (fst $ unzip texts) $ subfigs contents
   where
      columnise :: (Integer, FigText) -> Bool -> String
      columnise (n, text) hrule = 
         -- I haven't tested this overlay hackery beyond two minipages...
         (if forBeamer then onslide (show n ++ "-") "" else "") ++
         "\\begin{minipage}[t]{0.5\\textwidth}\n" ++ 
         showSubfig overlayRoot (n, text) ++            
         (if hrule then "\\hrule\n" else "") ++
         "\\end{minipage}%\n"
      subFloat :: Bool -> (String, (Integer, FigText)) -> String
      subFloat hrule (caption, (n, text)) = 
         "\\begin{SubFloat}{" ++ caption ++ "}\n" ++
         columnise (n, text) hrule ++
         "\\end{SubFloat}\n\\vspace{4pt}\n"

onslide :: String -> String -> String
onslide overlaySpec str =
   "\\onslide<" ++ overlaySpec ++ ">\n" ++
   if str == ""
   then ""
   else "{" ++ str ++ "}\n"

-- Wrap in Verbatim environment with suitable escape characters.
verbatim :: String -> String
verbatim str =
   (if forBeamer then "\\vspace{5pt}\n" else "") ++
   "{\\tiny\n\\begin{Verbatim}[commandchars=\\\\\\{\\},codes={\\catcode`$=3\\catcode`^=7}]\n" ++ 
   str ++ "\n\n" ++
   "\\end{Verbatim}\n%$\n}\n"
