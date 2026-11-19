module
public import DirectTypedContextConstructors
@[expose] public section
namespace RosserDirect.FramedRow
open FramedContext Membership

/-- Read through a context's empty-frame terminator, not its first internal
formula delimiter. This is the semantic specification of the finite scanner. -/
def readContext : Bool → List Symbol → List Symbol × List Symbol
 | _, [] => ([],[])
 | false, .frameEnd :: xs => ([.frameEnd],xs)
 | _, .frameEnd :: xs => let (p,r) := readContext false xs; (.frameEnd :: p,r)
 | _, x :: xs => let (p,r) := readContext true xs; (x :: p,r)

theorem read_inside (p : List Symbol) (valid : ∀ x ∈ p, x ≠ .frameEnd) (rest : List Symbol) :
 readContext true (p ++ .frameEnd :: rest) =
  let (c,r) := readContext false rest; (p ++ .frameEnd :: c,r) := by
 induction p with
 | nil => rfl
 | cons x xs ih =>
   have hx := valid x (by simp)
   have hi := ih (by intro y hy; exact valid y (by simp [hy]))
   cases x <;> simp_all [readContext]

theorem read_enter (p : ZFR.Formula) (rest : List Symbol) :
 readContext false (formulaPayload p ++ .frameEnd :: rest) =
  let (c,r) := readContext false rest; (formulaPayload p ++ .frameEnd :: c,r) := by
 obtain ⟨x,xs,hp⟩ := List.exists_cons_of_ne_nil (formula_nonempty p)
 have hv : ∀ y ∈ x :: xs, y ≠ .frameEnd := by rw [← hp]; exact payloadBits_no_end _
 have hi := read_inside xs (by intro y hy; exact hv y (by simp [hy])) rest
 have hx := hv x (by simp)
 rw [hp]
 cases x <;> simp_all [readContext]

theorem read_context (Γ : ZFR.Context) (rest : List Symbol) :
 readContext false (encode Γ ++ rest) = (encode Γ,rest) := by
 induction Γ with
 | nil => rfl
 | cons p Γ ih =>
   have h := read_enter p (encode Γ ++ rest)
   rw [ih] at h
   simpa [encode, contextFrames, frames, List.append_assoc] using h

def formulaFrame (p : ZFR.Formula) : List Symbol := formulaPayload p ++ [.frameEnd]

def encode : ZFR.Row → List Symbol
 | .seq Γ p => .bit0 :: (FramedContext.encode Γ ++ formulaFrame p)
 | .branches Γ p q r => .bit1 ::
   (FramedContext.encode Γ ++ formulaFrame p ++ formulaFrame q ++ formulaFrame r)

/-- Field recovery retains the trailing row stack. There is no dependence on
external input lengths or on a guessed delimiter position. -/
def readRow : List Symbol → Bool × List Symbol × List (List Symbol) × List Symbol
 | .bit0 :: xs =>
   let (c,ys) := readContext false xs
   let (p,rest) := readFrame ys
   (false,c,[p],rest)
 | .bit1 :: xs =>
   let (c,ys) := readContext false xs
   let (p,zs) := readFrame ys
   let (q,ws) := readFrame zs
   let (r,rest) := readFrame ws
   (true,c,[p,q,r],rest)
 | xs => (false,[],[],xs)

def fields : ZFR.Row → Bool × List Symbol × List (List Symbol)
 | .seq Γ p => (false,FramedContext.encode Γ,[formulaPayload p])
 | .branches Γ p q r => (true,FramedContext.encode Γ,[formulaPayload p,formulaPayload q,formulaPayload r])

theorem read_formula (p : ZFR.Formula) (rest : List Symbol) :
 readFrame (formulaFrame p ++ rest) = (formulaPayload p,rest) := by
 simpa [formulaFrame,List.append_assoc] using read_frame (formulaPayload p) (payloadBits_no_end _) rest

theorem read_row (r : ZFR.Row) (rest : List Symbol) :
 readRow (encode r ++ rest) = ((fields r).1,(fields r).2.1,(fields r).2.2,rest) := by
 cases r <;> simp only [encode, List.cons_append, List.append_assoc, readRow,
   read_context, read_formula, fields]

theorem fields_injective : Function.Injective fields := by
 intro a b h
 cases a with
 | seq Γ p =>
   cases b with
   | seq Δ q =>
     have hc : FramedContext.encode Γ = FramedContext.encode Δ := congrArg (fun x => x.2.1) h
     have hp : formulaPayload p = formulaPayload q := by simpa [fields] using congrArg (fun x => x.2.2) h
     exact congrArg₂ ZFR.Row.seq (encode_injective hc) (formulaPayload_injective hp)
   | branches Δ q r s => simp [fields] at h
 | branches Γ p q r =>
   cases b with
   | seq Δ s => simp [fields] at h
   | branches Δ s t u =>
     have hc : FramedContext.encode Γ = FramedContext.encode Δ := congrArg (fun x => x.2.1) h
     have hp : formulaPayload p = formulaPayload s ∧ formulaPayload q = formulaPayload t ∧ formulaPayload r = formulaPayload u := by
       simpa [fields] using congrArg (fun x => x.2.2) h
     have hg := encode_injective hc
     have h1 := formulaPayload_injective hp.1
     have h2 := formulaPayload_injective hp.2.1
     have h3 := formulaPayload_injective hp.2.2
     subst Δ; subst s; subst t; subst u; rfl

theorem encode_injective : Function.Injective encode := by
 intro a b h
 have hr := congrArg (fun s => readRow (s ++ [])) h
 rw [read_row, read_row] at hr
 apply fields_injective
 have h1 := congrArg Prod.fst hr
 have h2 := congrArg (fun x => x.2.1) hr
 have h3 := congrArg (fun x => x.2.2.1) hr
 exact Prod.ext h1 (Prod.ext h2 h3)

theorem exact_row_equality (a b : ZFR.Row) : encode a = encode b ↔ a = b :=
 ⟨fun h => encode_injective h, congrArg encode⟩

end RosserDirect.FramedRow
