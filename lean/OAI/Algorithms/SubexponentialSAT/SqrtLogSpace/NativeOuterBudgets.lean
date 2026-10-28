import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuter
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ResourceBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalCostAlgebra
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets

/-! The exact large-entry arithmetic join: paid canonical frontend, fixed
cutoff test, actual setup, disjoint DFS, full-word positivity and factor-seven
primitive compilation. These numerical bounds introduce no run contract. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
open OAI BitProgram StructuredCalls SqrtLog.Statement DisjointReuse

/-- Each actual source phase is lifted to one bound, once. -/
def entrySpace (n L inputBound bound : ℕ) : ℕ :=
  max (L+4000*(L+1)^2)
    (max (1224*(L+1)+10*n+28) (Native.outerSpace inputBound bound n))

/-- The exact upper bound obtained by composing the measured source phases
and then applying the actual guarded compiler's factor seven. -/
def entryTime (k n L body threshold leafTime inputBound bound visits setupSteps : ℕ) : ℕ :=
  7*(4000*(L+1)^2+10*n+29+setupSteps+
    Native.dfsTime k n body threshold leafTime bound visits+
    12*Native.outerBoundary inputBound bound n+14+1)

theorem entrySpace_requirements (n L inputBound bound : ℕ) :
    L+4000*(L+1)^2≤entrySpace n L inputBound bound ∧
    1224*(L+1)+10*n+28≤entrySpace n L inputBound bound ∧
    Native.outerSpace inputBound bound n≤entrySpace n L inputBound bound := by
  unfold entrySpace
  exact ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

private theorem boundary_le (n inputBound bound S : ℕ)
    (hn : n+1≤S) (hi : inputBound≤S) (hb : bound≤S) :
    Native.outerBoundary inputBound bound n≤1250*S := by
  unfold Native.outerBoundary
  exact max_le (by omega) (by omega)

/-- Space is polynomial in the original input word, independently of all
visit and leaf-runtime counts. The canonical entry is included. -/
theorem entrySpace_polynomial (K e : ℕ) :
    ∃ C d : ℕ, ∀ n L inputBound bound : ℕ,
      n≤L → inputBound≤K*(L+1)^e → bound≤K*(L+1)^e →
      entrySpace n L inputBound bound≤C*(L+1)^d := by
  refine ⟨2000000*(K+1),e+2,?_⟩
  intro n L inputBound bound hn hi hb
  let S := (K+1)*(L+1)^(e+2)
  have he : (L+1)^e≤(L+1)^(e+2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hx : L+1≤S := (Nat.le_self_pow (by omega) _).trans
    (Nat.le_mul_of_pos_left _ (by omega))
  have hx2 : (L+1)^2≤S :=
    (Nat.pow_le_pow_right (by omega) (show 2≤e+2 by omega)).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  have hiS : inputBound≤S := hi.trans (Nat.mul_le_mul (Nat.le_succ K) he)
  have hbS : bound≤S := hb.trans (Nat.mul_le_mul (Nat.le_succ K) he)
  have hboundary := boundary_le n inputBound bound S (by omega) hiS hbS
  have houter : Native.outerSpace inputBound bound n≤2000000*S := by
    unfold Native.outerSpace
    omega
  have hresult : entrySpace n L inputBound bound≤2000000*S := by
    unfold entrySpace
    exact max_le (by omega) (max_le (by omega) houter)
  simpa only [S,Nat.mul_assoc] using hresult

/-- The exact compiler envelope counts every primitive tape and every
visited prefix, including blank crossings and its fixed control overhead. -/
theorem primitiveSpace_polynomial (K e : ℕ) :
    ∃ C d : ℕ, ∀ n L inputBound bound : ℕ,
      n≤L → inputBound≤K*(L+1)^e → bound≤K*(L+1)^e →
      1220*(entrySpace n L inputBound bound+L+15)≤C*(L+1)^d := by
  obtain ⟨C,d,h⟩ := entrySpace_polynomial K e
  refine ⟨1220*(C+16),d+1,?_⟩
  intro n L inputBound bound hn hi hb
  exact compiledSpace_polynomial 1220 _ L C d (h n L inputBound bound hn hi hb)

/-- The startup body can be shorter than formulaBound. Every visit still
uses the genuine formulaBound budget, including losing selector scans. -/
theorem entryTime_le (k n L body threshold leafTime inputBound bound visits setupSteps S : ℕ)
    (hL : L+1≤S) (hn : n≤L)
    (hbody : body≤SparseCountProgram.formulaBound n k)
    (hformula : SparseCountProgram.formulaBound n k≤S)
    (ht : threshold≤S) (hi : inputBound≤S) (hb : bound≤S) (hsetup : setupSteps≤S) :
    entryTime k n L body threshold leafTime inputBound bound visits setupSteps≤
      225000000*(SparsePriorityProgram.Selector.selectorCoefficient k+1)*S^4*
        (visits+1)*(leafTime+1) := by
  let coefficient := SparsePriorityProgram.Selector.selectorCoefficient k
  have hS : 1≤S := by omega
  have hpow : S≤S^4 := Nat.le_self_pow (by decide) _
  have h1 : 1≤S^4 := one_le_pow₀ hS
  have hfront : 4000*(L+1)^2≤4000*S^4 := Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left hL 2).trans (Nat.pow_le_pow_right hS (by decide)))
  have hboundary := boundary_le n inputBound bound S (by omega) hi hb
  have hdfs := dfsCommandTime_le coefficient n (SparseCountProgram.formulaBound n k)
    threshold leafTime bound visits S (by omega) hformula ht hb
  dsimp only [coefficient] at hdfs
  have hactual : Native.dfsTime k n body threshold leafTime bound visits≤
      32000100*(coefficient+1)*S^4*(visits+1)*(leafTime+1) := by
    apply le_trans ?_ hdfs
    unfold Native.dfsTime DFSVisit.visitTime
    omega
  have hother : 4000*(L+1)^2+10*n+29+setupSteps+
      12*Native.outerBoundary inputBound bound n+14+1≤20000*S^4 := by omega
  have hR : 1≤(visits+1)*(leafTime+1) := Nat.mul_pos (by omega) (by omega)
  have hpaid : 20000*S^4≤20000*S^4*((visits+1)*(leafTime+1)) :=
    (Nat.mul_one _).symm.le.trans (Nat.mul_le_mul_left _ hR)
  unfold entryTime
  calc
    _ = 7*((4000*(L+1)^2+10*n+29+setupSteps+
      12*Native.outerBoundary inputBound bound n+14+1)+
      Native.dfsTime k n body threshold leafTime bound visits) := by ring
    _ ≤ 7*(20000*S^4*((visits+1)*(leafTime+1))+
      32000100*(coefficient+1)*S^4*(visits+1)*(leafTime+1)) :=
        Nat.mul_le_mul_left 7 (Nat.add_le_add (hother.trans hpaid) hactual)
    _ = (140000+224000700*(coefficient+1))*S^4*(visits+1)*(leafTime+1) := by ring
    _ ≤ _ := by dsimp only [coefficient]; gcongr; omega

/-- Constants and degree depend only on fixed width and the ordinary source
cap, before any formula, visited node, leaf or primitive run is selected. -/
theorem entryTime_polynomial (k K e : ℕ) :
    ∃ C d : ℕ, ∀ n L body threshold leafTime inputBound bound visits setupSteps : ℕ,
      n≤L → body≤SparseCountProgram.formulaBound n k →
      threshold≤K*(L+1)^e → inputBound≤K*(L+1)^e →
      bound≤K*(L+1)^e → setupSteps≤K*(L+1)^e →
      entryTime k n L body threshold leafTime inputBound bound visits setupSteps≤
        C*(L+1)^d*(visits+1)*(leafTime+1) := by
  let c := 2+(4+8*k)*(k+1)*2^k
  let A := c+K+1
  let D := k+e+2
  refine ⟨225000000*(SparsePriorityProgram.Selector.selectorCoefficient k+1)*A^4,D*4,?_⟩
  intro n L body threshold leafTime inputBound bound visits setupSteps hn hbody ht hi hb hsetup
  let S := A*(L+1)^D
  have hA : 1≤A := by dsimp [A]; omega
  have hL : L+1≤S := (Nat.le_self_pow (by dsimp [D]; omega) _).trans
    (Nat.le_mul_of_pos_left _ hA)
  have hcommon : K*(L+1)^e≤S := Nat.mul_le_mul (by dsimp [A]; omega)
    (Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega))
  have hformula : SparseCountProgram.formulaBound n k≤S := by
    apply (formulaBound_polynomial n k).trans
    apply Nat.mul_le_mul (show c≤A by dsimp [A]; omega)
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega))
  have h := entryTime_le k n L body threshold leafTime inputBound bound visits setupSteps S
    hL hn hbody hformula (ht.trans hcommon) (hi.trans hcommon) (hb.trans hcommon)
    (hsetup.trans hcommon)
  simpa only [S,mul_pow,←pow_mul,Nat.mul_assoc] using h

/-- The actual reciprocal-sparsification visits multiply the actual leaf
budget. Their exponents add; the ETH square-root-log scale stays unchanged. -/
theorem runtime_of_tree_and_leaf (k coefficient degree : ℕ)
    (leafConstant leafExponent : ℝ) (hC : 1≤leafConstant) (hA : 0≤leafExponent)
    (leafDegree : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ n L visits leafTime primitiveTime : ℕ,
      20 ≤ n → 1 ≤ sparsifySchedule n → n ≤ L →
      (visits : ℝ)≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide))*n+1 : ℕ) : ℝ)^2*
          (2 : ℝ)^((n : ℝ)/sparsifySchedule n) →
      (leafTime : ℝ)≤runtimeBound leafConstant leafExponent leafDegree L n →
      primitiveTime≤coefficient*(L+1)^degree*(visits+1)*(leafTime+1) →
      (primitiveTime : ℝ)≤runtimeBound C (256+leafExponent)
        (degree+(4*(k-2)+2)+leafDegree) L n := by
  obtain ⟨T,hT,htree⟩ := chosen_treeBudget_runtimeBound k
  refine ⟨4*((coefficient : ℝ)+1)*T*leafConstant,?_,?_⟩
  · have hcoeff : 1≤(coefficient : ℝ)+1 := by
      have := Nat.cast_nonneg (α := ℝ) coefficient
      linarith
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hcoeff) hT) hC
  intro n L visits leafTime primitiveTime hn hs hLn hvisits hleaf htime
  have hv := hvisits.trans (htree n L hn hs hLn)
  have hv1 := one_le_runtimeBound hT (by norm_num : (0 : ℝ)≤256)
    (4*(k-2)+2) L n
  have hl1 := one_le_runtimeBound hC hA leafDegree L n
  have hvplus : (visits : ℝ)+1≤2*runtimeBound T 256 (4*(k-2)+2) L n := by linarith
  have hlplus : (leafTime : ℝ)+1≤2*runtimeBound leafConstant leafExponent leafDegree L n := by linarith
  have hcast : (primitiveTime : ℝ)≤(coefficient : ℝ)*((L : ℝ)+1)^degree*
      ((visits : ℝ)+1)*((leafTime : ℝ)+1) := by exact_mod_cast htime
  calc
    _ ≤ (coefficient : ℝ)*((L : ℝ)+1)^degree*
      (2*runtimeBound T 256 (4*(k-2)+2) L n)*
      (2*runtimeBound leafConstant leafExponent leafDegree L n) := by
        apply hcast.trans
        gcongr
    _ ≤ 4*((coefficient : ℝ)+1)*((L : ℝ)+1)^degree*
      (runtimeBound T 256 (4*(k-2)+2) L n*
        runtimeBound leafConstant leafExponent leafDegree L n) := by
      have h := Nat.cast_nonneg (α := ℝ) coefficient
      have hp : 0≤((L : ℝ)+1)^degree := by positivity
      have ht0 := runtimeBound_nonneg (by linarith : 0≤T) 256 (4*(k-2)+2) L n
      have hl0 := runtimeBound_nonneg (by linarith : 0≤leafConstant) leafExponent leafDegree L n
      nlinarith only [mul_nonneg hp (mul_nonneg ht0 hl0)]
    _ = runtimeBound (4*((coefficient : ℝ)+1)*T*leafConstant) (256+leafExponent)
        (degree+(4*(k-2)+2)+leafDegree) L n := by
      rw [SqrtLog.Execution.FinalCost.runtimeBound_product]
      unfold runtimeBound
      rw [pow_add,pow_add]
      ring

/-- One fixed cap simultaneously satisfies actual startup, visits, the local
leaf, classification and power setup. It is chosen before any input or run. -/
theorem globalBound_polynomial (k Ki ei Kl el : ℕ) :
    ∃ C e : ℕ, 1≤C ∧ ∀ n m L body inputBound threshold localBound : ℕ,
      n≤L → m≤L → body≤SparseCountProgram.formulaBound n k →
      inputBound≤Ki*(L+1)^ei → threshold ≤ inputBound →
      localBound≤Kl*(L+1)^el →
      1220*inputBound+8*body+17≤C*(L+1)^e ∧
      DFSCountProgram.visitSpace k n m threshold≤C*(L+1)^e ∧
      localBound≤C*(L+1)^e ∧
      101*SparseCountProgram.formulaBound n k+103≤C*(L+1)^e ∧
      5*n+6≤C*(L+1)^e := by
  obtain ⟨Cv,dv,hv⟩ := dfsVisitSpace_polynomial k
    (SparsePriorityProgram.Selector.selectorCoefficient k) Ki ei
  let c := 2+(4+8*k)*(k+1)*2^k
  let C := 1220*Ki+109*c+Cv+Kl+131
  let e := ei+el+dv+k+2
  refine ⟨C,e,by dsimp [C]; omega,?_⟩
  intro n m L body inputBound threshold localBound hn hm hbody hi ht hl
  let P := (L+1)^e
  have h1 : 1≤P := Nat.one_le_pow' _ _
  have hnP : n≤P := hn.trans ((Nat.le_succ L).trans
    (Nat.le_self_pow (by dsimp [e]; omega) _))
  have hiP : inputBound≤Ki*P := hi.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega)))
  have hlP : localBound≤Kl*P := hl.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega)))
  have hf : SparseCountProgram.formulaBound n k≤c*P := by
    apply (formulaBound_polynomial n k).trans
    apply Nat.mul_le_mul_left c
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega))
  have hvP : DFSCountProgram.visitSpace k n m threshold≤Cv*P := by
    apply (hv n m L threshold hn hm (ht.trans hi)).trans
    exact Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega))
  have hstart : 1220*inputBound+8*body+17≤(1220*Ki+8*c+17)*P := by
    rw [add_mul,add_mul]
    simp only [Nat.mul_assoc]
    omega
  have hclass : 101*SparseCountProgram.formulaBound n k+103≤(101*c+103)*P := by
    rw [add_mul]
    simp only [Nat.mul_assoc]
    omega
  have hpower : 5*n+6≤11*P := by omega
  exact ⟨hstart.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega)),
    hvP.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega)),
    hlP.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega)),
    hclass.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega)),
    hpower.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega))⟩

/-- The actual leaf wrapper's linear global-cap work and rounded local time
preserve the same exponential scale. The chosen cap depends only on input
length, and the rounding is confined to this proof-side time bound. -/
theorem leafTime_runtimeBound (k K globalDegree : ℕ) (C A : ℝ)
    (hC : 1≤C) (hA : 0≤A) (degree : ℕ) :
    ∃ D : ℝ, ∃ e : ℕ, 1≤D ∧ ∀ n L bound : ℕ,
      n≤L → bound≤K*(L+1)^globalDegree →
      ((3624*bound+100*(SparseCountProgram.formulaBound n k+1)+11*n+
        Nat.ceil (runtimeBound C A degree L n)+5479 : ℕ) : ℝ)≤
        runtimeBound D A e L n := by
  let c := 2+(4+8*k)*(k+1)*2^k
  let overhead := 3624*K+100*c+5590
  let power := globalDegree+k+1
  refine ⟨2*C+overhead,degree+power,?_,?_⟩
  · have := Nat.cast_nonneg (α := ℝ) overhead
    linarith
  intro n L bound hn hb
  let P := (L+1)^power
  have h1 : 1≤P := Nat.one_le_pow' _ _
  have hnP : n≤P := hn.trans ((Nat.le_succ L).trans
    (Nat.le_self_pow (by dsimp [power]; omega) _))
  have hbP : bound≤K*P := hb.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (by dsimp [power]; omega)))
  have hf : SparseCountProgram.formulaBound n k≤c*P := by
    apply (formulaBound_polynomial n k).trans
    apply Nat.mul_le_mul_left c
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [power]; omega))
  have hextra : 3624*bound+100*(SparseCountProgram.formulaBound n k+1)+11*n+5479≤
      overhead*(L+1)^power := by
    change _≤overhead*P
    dsimp only [overhead]
    rw [add_mul,add_mul]
    simp only [Nat.mul_assoc]
    omega
  have hcore : (Nat.ceil (runtimeBound C A degree L n) : ℝ)≤
      runtimeBound (2*C) A degree L n := by
    simpa only [runtimeBound_mul_constant] using
      SqrtLog.Execution.ceil_runtimeBound_le hC hA degree L n
  have h := QueryStreamBudgets.polynomial_overhead_runtime (2*C) A degree overhead power
    L n (Nat.ceil (runtimeBound C A degree L n))
    (3624*bound+100*(SparseCountProgram.formulaBound n k+1)+11*n+5479)
    (by linarith) hA hcore hextra
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

/-- One positive triple of constants covers both the actual large-run time
and the fixed finite fallback, uniformly including ambient n=0. -/
theorem runtime_with_fallback (C A : ℝ) (d : ℕ) (hC : 1≤C) (hA : 0≤A) :
    0<C+28700 ∧ 0<A+1 ∧ 0<d+2 ∧ ∀ n L : ℕ,
      runtimeBound C A d L n≤runtimeBound (C+28700) (A+1) (d+2) L n ∧
      ((28700*(L+1)^2 : ℕ) : ℝ)≤runtimeBound (C+28700) (A+1) (d+2) L n := by
  refine ⟨by linarith,by linarith,by omega,?_⟩
  intro n L
  have hsum : runtimeBound C A d L n+runtimeBound 28700 0 2 L n≤
      runtimeBound (C+28700) (A+1) (d+2) L n := by
    apply (QueryStreamBudgets.runtimeBound_add_bound C 28700 A 0 d 2 L n
      (by linarith) (by norm_num) hA (by norm_num)).trans
    simpa only [add_zero] using runtimeBound_mono_exponent
      (by linarith : 0≤C+28700) (by linarith : A≤A+1) (d+2) L n
  refine ⟨(le_add_of_nonneg_right (runtimeBound_nonneg (by norm_num) 0 2 L n)).trans hsum,?_⟩
  have h := (le_add_of_nonneg_left
    (runtimeBound_nonneg (by linarith : 0≤C) A d L n)).trans hsum
  simpa only [runtimeBound,zero_mul,Real.rpow_zero,mul_one,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using h

/-- The same fixed positive polynomial covers all large primitive visited
space and the actual finite fallback. No runtime or visit count is used. -/
theorem space_with_fallback (S : ℝ) (e : ℕ) (hS : 0≤S) :
    0<S+5022741 ∧ 0<e+2 ∧ ∀ L : ℕ,
      S*((L : ℝ)+1)^e≤(S+5022741)*((L : ℝ)+1)^(e+2) ∧
      ((5022740*(L+1)^2 : ℕ) : ℝ)≤(S+5022741)*((L : ℝ)+1)^(e+2) := by
  refine ⟨by linarith,by omega,?_⟩
  intro L
  have hbase : (1 : ℝ)≤(L : ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have he := pow_le_pow_right₀ hbase (show e≤e+2 by omega)
  have htwo := pow_le_pow_right₀ hbase (show 2≤e+2 by omega)
  refine ⟨mul_le_mul (by linarith) he (by positivity) (by linarith),?_⟩
  have h : (5022740 : ℝ)*((L : ℝ)+1)^2≤(S+5022741)*((L : ℝ)+1)^(e+2) :=
    mul_le_mul (by linarith) htwo (by positivity) (by linarith)
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
