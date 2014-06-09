import qualified Unify
import qualified Infer

s :: Infer.Term
s = Infer.AbsT "x"
      (Infer.AbsT "y"
        (Infer.AbsT "z"
          (Infer.AppT
            (Infer.AppT
              (Infer.VarT "x")
              (Infer.VarT "z"))
            (Infer.AppT
              (Infer.VarT "y")
              (Infer.VarT "z")))))

main :: IO ()
main = do
  case Infer.inferType s of
    Right tt -> print (Infer.typeof tt)
    Left err -> print err
