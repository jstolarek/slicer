module SlicerTestSuiteUtils where

import           System.FilePath   ( joinPath, pathSeparator             )
import           System.IO         ( IOMode(..), openFile                )
import           System.Process    ( CreateProcess(..), StdStream(..)
                                   , createProcess, proc, waitForProcess )
import           Test.Tasty        ( TestTree                            )
import           Test.Tasty.Golden ( goldenVsFileDiff                    )

-- directory storing *.tml test files
tmlFilesPath :: FilePath
tmlFilesPath = joinPath [ "tests", "tml" ]

-- directory storing golden files
goldenPath :: FilePath
goldenPath = joinPath [ "tests", "tml", "golden-templates" ]

-- path to slicer executable relative to goldenPath (hence going three
-- directories up)
slicerPath :: FilePath
slicerPath = joinPath [ "..", "..", "..", "dist", "build", "slicer", "slicer" ]

-- Executes a single test by running a TML file and comparing the actual output
-- with the expected one.
runTMLTest :: FilePath -> TestTree
runTMLTest testName =
    goldenVsFileDiff
      testName
      (\ref new -> ["diff", "-w", "-B", ref, new]) -- see Note [Diff options]
      goldenFilePath
      actualFilePath
      runTMLFile
    where
      testFile       = ".."       ++ [pathSeparator] ++ testName ++ ".tml"
      goldenFilePath = goldenPath ++ [pathSeparator] ++ testName ++ ".golden"
      actualFilePath = goldenPath ++ [pathSeparator] ++ testName ++ ".actual"

      runTMLFile :: IO ()
      runTMLFile = do
        hActualFile <- openFile actualFilePath WriteMode
        (_, _, _, pid) <- createProcess (proc slicerPath [testFile])
                                              { std_out = UseHandle hActualFile
                                              , std_err = UseHandle hActualFile
                                              , cwd     = Just goldenPath }
        _ <- waitForProcess pid -- see Note [Ignore exit code]
        return ()

-- Note [Diff options]
-- ~~~~~~~~~~~~~~~~~~~
--
-- We use following diff options:
--  -w - Ignore all white space.
--  -B - Ignore changes whose lines are all blank.

-- Note [Ignore exit code]
-- ~~~~~~~~~~~~~~~~~~~~~~~
--
-- It may happen that compilation of a TML file fails. We could find out
-- whether that happened by inspecting the exit code of Slicer process. But it
-- would be tricky to get a helpful message from the failing test: we would need
-- to display stderr which we just wrote into a file. Luckliy we don't have to
-- do that - we can ignore the problem here and let the test fail when the
-- actual file is compared with the golden file.
