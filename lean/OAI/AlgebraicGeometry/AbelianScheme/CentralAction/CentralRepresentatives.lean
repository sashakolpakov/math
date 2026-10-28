import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Central Representatives -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction

noncomputable section

/-! Actual central representatives and their raw spherical operators.
All three block exponents coincide; the opposite exponent is h - a v.
The construction uses inverse representatives, as in TateComparison. -/

open scoped Classical

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

def centralType {s : ℕ} (a : Fin s → ℤ) (h : ℤ) : TateComparison.Local.LocalType s where
  multiplier := h
  exponent v _ := a v
  dominant _ _ _ _ := le_rfl

def centralRepresentative (s q : ℕ) [Fact q.Prime]
    (a : Fin s → ℤ) (h : ℤ) : TateComparison.HeckeKernel.SplitGroup s q :=
  (fun v => Matrix.GeneralLinearGroup.scalar (Fin 3) (TateComparison.HeckeKernel.qUnit q ^ a v), TateComparison.HeckeKernel.qUnit q ^ h)

theorem centralRepresentative_commutes (s q : ℕ) [Fact q.Prime]
    (a : Fin s → ℤ) (h : ℤ) (g : TateComparison.HeckeKernel.SplitGroup s q) :
    Commute g (centralRepresentative s q a h) := by
  apply Prod.ext
  · funext v
    exact (Matrix.GeneralLinearGroup.scalar_commute (TateComparison.HeckeKernel.qUnit q ^ a v) (g.1 v)).symm
  · exact mul_comm _ _

theorem representative_centralType (s q : ℕ) [Fact q.Prime]
    (a : Fin s → ℤ) (h : ℤ) :
    TateComparison.HeckeKernel.representative s q (centralType a h) = centralRepresentative s q a h := by
  apply Prod.ext
  · funext v
    apply Units.ext
    rfl
  · rfl

def centralCoset (s q : ℕ) [Fact q.Prime] (a : Fin s → ℤ) (h : ℤ) : TateComparison.HeckeKernel.Hecke s q :=
  (TateComparison.HeckeKernel.centralHeckeUnit (TateComparison.HeckeKernel.integralLevel s q) (centralRepresentative s q a h)
    (centralRepresentative_commutes s q a h)).val

/-- The central double coset really is its unnormalized characteristic
function. This proves compatibility with TateComparison's independently supplied basis. -/
theorem centralHeckeUnit_isRaw {G : Type*} [Group G] (U : Subgroup G)
    (z : G) (hz : ∀ g : G, Commute g z) :
    TateComparison.HeckeKernel.IsRawDoubleCoset U z (TateComparison.HeckeKernel.centralHeckeUnit U z hz).val := by
  intro x
  rw [TateComparison.HeckeKernel.centralHeckeUnit_kernel]
  have hiff : (QuotientGroup.mk z⁻¹ : G ⧸ U) = QuotientGroup.mk x ↔
      ∃ k l : U, x = (k : G) * z⁻¹ * (l : G) := by
    rw [QuotientGroup.eq]
    simp only [inv_inv]
    constructor
    · intro hx
      refine ⟨1, ⟨z * x, hx⟩, ?_⟩
      simp
    · rintro ⟨k, l, rfl⟩
      have he : z * ((k : G) * z⁻¹ * (l : G)) = (k : G) * (l : G) := by
        rw [← mul_assoc, ← mul_assoc, ← (hz k).eq]
        simp [mul_assoc]
      rw [he]
      exact U.mul_mem k.property l.property
  classical
  simp only [Finsupp.single_apply, hiff]

theorem centralCoset_isRaw (s q : ℕ) [Fact q.Prime]
    (a : Fin s → ℤ) (h : ℤ) :
    TateComparison.HeckeKernel.IsRawDoubleCoset (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q (centralType a h))
      (centralCoset s q a h) := by
  rw [representative_centralType]
  exact centralHeckeUnit_isRaw _ _ _

theorem centralCoset_eq_basis (s q : ℕ) [Fact q.Prime]
    (basis : TateComparison.Local.LocalType s → TateComparison.HeckeKernel.Hecke s q)
    (hbasis : ∀ t, TateComparison.HeckeKernel.IsRawDoubleCoset (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t) (basis t))
    (a : Fin s → ℤ) (h : ℤ) :
    centralCoset s q a h = basis (centralType a h) :=
  TateComparison.HeckeKernel.rawDoubleCoset_unique _ (centralCoset_isRaw s q a h) (hbasis _)

theorem centralRepresentative_mul (s q : ℕ) [Fact q.Prime]
    (a b : Fin s → ℤ) (h k : ℤ) :
    centralRepresentative s q a h * centralRepresentative s q b k =
      centralRepresentative s q (fun v => a v + b v) (h + k) := by
  apply Prod.ext
  · funext v
    change Matrix.GeneralLinearGroup.scalar (Fin 3) (TateComparison.HeckeKernel.qUnit q ^ a v) *
      Matrix.GeneralLinearGroup.scalar (Fin 3) (TateComparison.HeckeKernel.qUnit q ^ b v) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (TateComparison.HeckeKernel.qUnit q ^ (a v + b v))
    rw [← map_mul, ← zpow_add]
  · exact (zpow_add (TateComparison.HeckeKernel.qUnit q) h k).symm

theorem centralCoset_mul (s q : ℕ) [Fact q.Prime]
    (a b : Fin s → ℤ) (h k : ℤ) :
    centralCoset s q a h * centralCoset s q b k =
      centralCoset s q (fun v => a v + b v) (h + k) := by
  apply Subtype.ext
  change TateComparison.HeckeKernel.translate (TateComparison.HeckeKernel.integralLevel s q) (centralRepresentative s q a h)⁻¹ *
      TateComparison.HeckeKernel.translate (TateComparison.HeckeKernel.integralLevel s q) (centralRepresentative s q b k)⁻¹ =
    TateComparison.HeckeKernel.translate (TateComparison.HeckeKernel.integralLevel s q)
      (centralRepresentative s q (fun v => a v + b v) (h + k))⁻¹
  rw [← TateComparison.HeckeKernel.translate_mul, ← centralRepresentative_mul, mul_inv_rev]
  congr 1
  exact ((centralRepresentative_commutes s q a h
    (centralRepresentative s q b k)).inv_inv).eq.symm

def t3Exponents {s : ℕ} (active : Fin s) : Fin s → ℤ :=
  fun v => if v = active then 1 else 0

def c0Exponents {s : ℕ} (active : Fin s) (fullSide : Fin s → Bool) : Fin s → ℤ :=
  fun v => if v ≠ active ∧ fullSide v = true then 1 else 0

def T3 (s q : ℕ) [Fact q.Prime] (active : Fin s) : TateComparison.HeckeKernel.Hecke s q :=
  centralCoset s q (t3Exponents active) 0

def C0 (s q : ℕ) [Fact q.Prime] (active : Fin s) (fullSide : Fin s → Bool) : TateComparison.HeckeKernel.Hecke s q :=
  centralCoset s q (c0Exponents active fullSide) 1

/-- One q-scalar central shift clears T3's negative opposite exponents. -/
def clearedT3Type {s : ℕ} (active : Fin s) : TateComparison.Local.IntegralType s :=
  ⟨centralType (fun v => t3Exponents active v + 1) 2, by
    refine ⟨by norm_num [centralType], ?_⟩
    intro v i
    simp only [centralType, t3Exponents]
    split_ifs <;> norm_num⟩

def c0IntegralType {s : ℕ} (active : Fin s) (fullSide : Fin s → Bool) : TateComparison.Local.IntegralType s :=
  ⟨centralType (c0Exponents active fullSide) 1, by
    refine ⟨by norm_num [centralType], ?_⟩
    intro v i
    simp only [centralType, c0Exponents]
    split_ifs <;> norm_num⟩

theorem clearedT3_coset (s q : ℕ) [Fact q.Prime] (active : Fin s) :
    T3 s q active * centralCoset s q (fun _ => 1) 2 =
      centralCoset s q (fun v => t3Exponents active v + 1) 2 := by
  exact centralCoset_mul s q (t3Exponents active) (fun _ => 1) 0 2

theorem centralCoset_scalar (s q : ℕ) [Fact q.Prime] :
    centralCoset s q (fun _ => 1) 2 = (TateComparison.HeckeKernel.scalarHeckeUnit s q).val := by
  have he : centralRepresentative s q (fun _ => 1) 2 = TateComparison.HeckeKernel.centralElement s q := by
    apply Prod.ext
    · funext v
      simp [centralRepresentative, TateComparison.HeckeKernel.centralElement]
    · simp [centralRepresentative, TateComparison.HeckeKernel.centralElement]
  apply Subtype.ext
  change TateComparison.HeckeKernel.translate (TateComparison.HeckeKernel.integralLevel s q) (centralRepresentative s q (fun _ => 1) 2)⁻¹ =
    TateComparison.HeckeKernel.translate (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.centralElement s q)⁻¹
  rw [he]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction
