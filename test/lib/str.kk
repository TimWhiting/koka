extern import
  c file "str-inline.c"

extern manage-string(str: string): ()
  c "kk_manage_string"

fun main()
  val l = "Hello World!".manage-string
  l.show.println
