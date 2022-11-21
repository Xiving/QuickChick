let flag_debug = Summary.ref ~name:"QC_flag_debug" false

let qcfail s = failwith (Printf.sprintf "Internal QuickChick Error : %s" s)

let msg_debug   s = if true then Feedback.msg_debug   s else ()
