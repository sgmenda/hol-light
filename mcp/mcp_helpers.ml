(* MCP helpers: JSON serialization for HOL Light goal states.
   Loaded via #use after HOL Light starts. No external dependencies. *)

(* Private copies of HOL Light's goal combinators so the MCP proof path is
   immune to a user shadowing g/e/b/r in their own eval (e.g. `let g = ...`).
   Defined in terms of the lower-level primitives (refine/by/VALID/set_goal/
   rotate) rather than aliasing g/e/b/r, so they don't depend on those names
   being unshadowed at load time. Kept in sync with tactics.ml. *)
let mcp_e tac = refine (by (VALID tac));;
let mcp_r n = refine (rotate n);;
let mcp_b () =
  let l = !current_goalstack in
  if length l = 1 then failwith "Can't back up any more" else
  (current_goalstack := tl l; !current_goalstack);;
let mcp_g t =
  let fvs = sort (<) (map (fst o dest_var) (frees t)) in
  (if fvs <> [] then
     warn true ("Free variables in goal: " ^ end_itlist (fun s t -> s ^ ", " ^ t) fvs));
  set_goal ([], t);;

let mcp_json_escape s =
  let buf = Buffer.create (String.length s + 16) in
  String.iter (fun c -> match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
        Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c) s;
  Buffer.contents buf;;

let mcp_json_string s = "\"" ^ mcp_json_escape s ^ "\"";;

let mcp_json_error msg = "{\"error\":" ^ mcp_json_string msg ^ "}";;

let mcp_buf_json_string buf s =
  Buffer.add_char buf '"';
  String.iter (fun c -> match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
        Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c) s;
  Buffer.add_char buf '"';;

let mcp_buf_goal buf ((asl, w) : goal) =
  Buffer.add_string buf "{\"hypotheses\":[";
  let first = ref true in
  List.iter (fun (label, th) ->
    if !first then first := false else Buffer.add_char buf ',';
    Buffer.add_string buf "{\"label\":";
    mcp_buf_json_string buf label;
    Buffer.add_string buf ",\"term\":";
    mcp_buf_json_string buf (string_of_term (concl th));
    Buffer.add_char buf '}'
  ) (List.rev asl);
  Buffer.add_string buf "],\"conclusion\":";
  mcp_buf_json_string buf (string_of_term w);
  Buffer.add_char buf '}';;

let mcp_buf_goals buf gl =
  Buffer.add_char buf '[';
  let first = ref true in
  List.iter (fun g ->
    if !first then first := false else Buffer.add_char buf ',';
    mcp_buf_goal buf g
  ) gl;
  Buffer.add_char buf ']';;

let mcp_json_goalstate () =
  let buf = Buffer.create 256 in
  (match !current_goalstack with
  | [] ->
    Buffer.add_string buf "{\"goals\":[],\"num_subgoals\":0,\"total_goals\":0}"
  | [_, gl, _] ->
    let n = List.length gl in
    Buffer.add_string buf "{\"goals\":";
    mcp_buf_goals buf gl;
    Buffer.add_string buf ",\"num_subgoals\":";
    Buffer.add_string buf (string_of_int (min 1 n));
    Buffer.add_string buf ",\"total_goals\":";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_char buf '}'
  | (_, gl, _) :: (_, gl0, _) :: _ ->
    let n = List.length gl in
    let p = n - List.length gl0 in
    let num_sub = if p < 1 then 1 else p + 1 in
    Buffer.add_string buf "{\"goals\":";
    mcp_buf_goals buf gl;
    Buffer.add_string buf ",\"num_subgoals\":";
    Buffer.add_string buf (string_of_int num_sub);
    Buffer.add_string buf ",\"total_goals\":";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_char buf '}');
  Buffer.contents buf;;

let mcp_json_after_tactic () =
  match !current_goalstack with
  | (_, [], f) :: _ ->
    let th = f null_inst [] in
    "{\"proved\":true,\"theorem\":" ^ mcp_json_string (string_of_thm th) ^ "}"
  | _ -> mcp_json_goalstate ();;

(* Cheap structural summary of the goal state: sizes and a truncated
   conclusion head, without serializing hypothesis terms. Lets a caller see
   the shape of a large goal (e.g. 60KB+ AES-tweak terms) without spending the
   output budget on the full goal_state dump. *)
let mcp_buf_goal_summary buf head_chars ((asl, w) : goal) =
  let c = string_of_term w in
  let clen = String.length c in
  let head =
    if clen <= head_chars then c
    else (String.sub c 0 head_chars) ^ "..." in
  Buffer.add_string buf "{\"num_hyps\":";
  Buffer.add_string buf (string_of_int (List.length asl));
  Buffer.add_string buf ",\"conclusion_chars\":";
  Buffer.add_string buf (string_of_int clen);
  Buffer.add_string buf ",\"conclusion_head\":";
  mcp_buf_json_string buf head;
  Buffer.add_char buf '}';;

let mcp_json_goal_summary head_chars =
  let buf = Buffer.create 256 in
  (match !current_goalstack with
  | [] ->
    Buffer.add_string buf
      "{\"goals\":[],\"num_subgoals\":0,\"total_goals\":0}"
  | gs ->
    let gl = match gs with (_, gl, _) :: _ -> gl | [] -> [] in
    let n = List.length gl in
    let num_sub = match gs with
      | [_, _, _] -> min 1 n
      | (_, _, _) :: (_, gl0, _) :: _ ->
        let p = n - List.length gl0 in
        if p < 1 then 1 else p + 1
      | [] -> 0 in
    Buffer.add_string buf "{\"goals\":[";
    let first = ref true in
    List.iter (fun g ->
      if !first then first := false else Buffer.add_char buf ',';
      mcp_buf_goal_summary buf head_chars g
    ) gl;
    Buffer.add_string buf "],\"num_subgoals\":";
    Buffer.add_string buf (string_of_int num_sub);
    Buffer.add_string buf ",\"total_goals\":";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_char buf '}');
  Buffer.contents buf;;

(* Fetch a single hypothesis of the top goal by 0-based index, so a caller can
   read one large hypothesis term without dumping all of them. Index order
   matches goal_state (List.rev of the internal assumption list). *)
let mcp_json_hypothesis idx =
  match !current_goalstack with
  | [] -> mcp_json_error "no goal in progress"
  | (_, [], _) :: _ -> mcp_json_error "goal is already proved (no subgoals)"
  | (_, (asl, _) :: _, _) :: _ ->
    let hyps = List.rev asl in
    let n = List.length hyps in
    if idx < 0 || idx >= n then
      mcp_json_error
        (Printf.sprintf "hypothesis index %d out of range (0..%d)" idx (n - 1))
    else
      let (label, th) = List.nth hyps idx in
      let buf = Buffer.create 256 in
      Buffer.add_string buf "{\"index\":";
      Buffer.add_string buf (string_of_int idx);
      Buffer.add_string buf ",\"label\":";
      mcp_buf_json_string buf label;
      Buffer.add_string buf ",\"term\":";
      mcp_buf_json_string buf (string_of_term (concl th));
      Buffer.add_char buf '}';
      Buffer.contents buf;;

let mcp_json_backtrack n =
  try
    for _ = 1 to n do ignore (mcp_b ()) done;
    mcp_json_goalstate ()
  with
  | Failure msg -> mcp_json_error msg
  | e -> mcp_json_error (Printexc.to_string e);;


(* Rebuild an earlier proof state by resetting the goalstack to its initial
   (bottom) goalstate and replaying the given tactic prefix in a single
   round-trip. Used as a fallback for backtrack when mcp_b() cannot rewind
   past the set_goal boundary but a recording of the tactics exists. The
   caller (server.py) supplies the prefix of tactics to keep. *)
let mcp_json_backtrack_replay (tacs : tactic list) =
  match !current_goalstack with
  | [] -> mcp_json_error "no goal to rewind"
  | l ->
    (try
      let initial = List.nth l (List.length l - 1) in
      current_goalstack := [initial];
      List.iter (fun tac -> ignore (mcp_e tac)) tacs;
      mcp_json_after_tactic ()
    with
    | Failure msg -> mcp_json_error msg
    | e -> mcp_json_error (Printexc.to_string e));;

let mcp_json_search pat limit =
  let results = search [name pat] in
  let buf = Buffer.create 512 in
  Buffer.add_char buf '[';
  let first = ref true in
  let count = ref 0 in
  List.iter (fun (n, th) ->
    if !count < limit then begin
      if !first then first := false else Buffer.add_char buf ',';
      Buffer.add_string buf "{\"name\":";
      mcp_buf_json_string buf n;
      Buffer.add_string buf ",\"statement\":";
      mcp_buf_json_string buf (string_of_thm th);
      Buffer.add_char buf '}';
      incr count
    end
  ) results;
  Buffer.add_char buf ']';
  Buffer.contents buf;;

let mcp_json_apply_tactics (tacs : tactic list) =
  let steps = ref 0 in
  try
    let proved = ref false in
    List.iter (fun tac ->
      if not !proved then begin
        ignore (mcp_e tac);
        incr steps;
        match !current_goalstack with
        | (_, [], _) :: _ -> proved := true
        | _ -> ()
      end
    ) tacs;
    if !proved then
      let th = match !current_goalstack with
        | (_, [], f) :: _ -> f null_inst []
        | _ -> failwith "unreachable" in
      "{\"proved\":true,\"theorem\":" ^ mcp_json_string (string_of_thm th) ^
      ",\"steps\":" ^ string_of_int !steps ^ "}"
    else
      let buf = Buffer.create 256 in
      (match !current_goalstack with
      | [] ->
        Buffer.add_string buf "{\"goals\":[],\"num_subgoals\":0,\"total_goals\":0"
      | [_, gl, _] ->
        let n = List.length gl in
        Buffer.add_string buf "{\"goals\":";
        mcp_buf_goals buf gl;
        Buffer.add_string buf ",\"num_subgoals\":";
        Buffer.add_string buf (string_of_int (min 1 n));
        Buffer.add_string buf ",\"total_goals\":";
        Buffer.add_string buf (string_of_int n)
      | (_, gl, _) :: (_, gl0, _) :: _ ->
        let n = List.length gl in
        let p = n - List.length gl0 in
        let num_sub = if p < 1 then 1 else p + 1 in
        Buffer.add_string buf "{\"goals\":";
        mcp_buf_goals buf gl;
        Buffer.add_string buf ",\"num_subgoals\":";
        Buffer.add_string buf (string_of_int num_sub);
        Buffer.add_string buf ",\"total_goals\":";
        Buffer.add_string buf (string_of_int n));
      Buffer.add_string buf ",\"steps\":";
      Buffer.add_string buf (string_of_int !steps);
      Buffer.add_char buf '}';
      Buffer.contents buf
  with
  | Failure msg ->
    "{\"error\":" ^ mcp_json_string msg ^
    ",\"step\":" ^ string_of_int !steps ^ "}"
  | e ->
    "{\"error\":" ^ mcp_json_string (Printexc.to_string e) ^
    ",\"step\":" ^ string_of_int !steps ^ "}";;

(* Quiet HOL Light's per-step "CPU time" chatter, which otherwise bloats every
   tool's output up to the sentinel. This is re-applied on every process start
   because helpers are #use'd afresh after each (re)start. *)
report_timing := false;;

Printf.printf "MCP helpers loaded.\n%!";;
