data Format = FmtInt Format
            | FmtChar Format
            | FmtString Format
            | FmtLit String Format
            | FmtDouble Format
            | End

parseFormatString : (str : String) -> Format
parseFormatString str = toFormat (unpack str)
  where toFormat : List Char -> Format
        toFormat [] = End
        toFormat ('%' :: 'd' :: xs) = FmtInt (toFormat xs)
        toFormat ('%' :: 'c' :: xs) = FmtChar (toFormat xs)
        toFormat ('%' :: 's' :: xs) = FmtString (toFormat xs)
        toFormat ('%' :: 'f' :: xs) = FmtDouble (toFormat xs)
        toFormat (x :: xs) = case toFormat xs of
                                  (FmtLit lit fmt) => FmtLit (strCons x lit) fmt
                                  fmt => FmtLit (strCons x "") fmt

PrintfType : Format -> Type
PrintfType (FmtInt fmt) = Int -> PrintfType fmt
PrintfType (FmtChar fmt) = Char -> PrintfType fmt
PrintfType (FmtString fmt) = String -> PrintfType fmt
PrintfType (FmtLit str fmt) = PrintfType fmt
PrintfType (FmtDouble fmt) = Double -> PrintfType fmt
PrintfType End = IO ()

printFormat : (format : Format) -> (acc : String) -> PrintfType format
printFormat (FmtInt fmt) acc = \num => printFormat fmt (acc ++ show num)
printFormat (FmtChar fmt) acc = \ch => printFormat fmt (acc ++ strCons ch "")
printFormat (FmtString fmt) acc = \str => printFormat fmt (acc ++ str)
printFormat (FmtLit str fmt) acc = printFormat fmt (acc ++ str)
printFormat (FmtDouble fmt) acc = \num => printFormat fmt (acc ++ show num)
printFormat End acc = putStr acc

printf : (format : String) -> PrintfType (parseFormatString format)
printf format = printFormat _ ""
