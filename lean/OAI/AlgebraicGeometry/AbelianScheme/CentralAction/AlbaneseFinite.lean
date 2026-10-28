import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredSideFinite
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseExt

/-! # Albanese Finite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseFinite.Construction

noncomputable section

/-! Identity of an actual central correspondence on the full moduli
scheme forces identity on the product Albanese by point push and IntegralModel
generation. This transfers finite order to the raw central actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem centralCoset_zero (s q : ℕ) [Fact q.Prime] :
    CentralRepresentatives.Construction.centralCoset s q (fun _ => 0) 0 = 1 := by
  have h : CentralRepresentatives.Construction.centralRepresentative s q (fun _ => 0) 0 = 1 := by
    simp [CentralRepresentatives.Construction.centralRepresentative]
    rfl
  apply Subtype.ext
  change TateComparison.HeckeKernel.translate (TateComparison.HeckeKernel.integralLevel s q) (CentralRepresentatives.Construction.centralRepresentative s q (fun _ => 0) 0)⁻¹ = 1
  rw [h, inv_one, TateComparison.HeckeKernel.translate_one]

theorem centralCoset_pow (s q : ℕ) [Fact q.Prime] (a : Fin s → ℤ) (h : ℤ) (n : ℕ) :
    CentralRepresentatives.Construction.centralCoset s q a h ^ n = CentralRepresentatives.Construction.centralCoset s q (fun v => a v * n) (h * n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero]
    exact (centralCoset_zero s q).symm
  | succ n ih =>
    rw [pow_succ, ih, CentralRepresentatives.Construction.centralCoset_mul]
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
  (hgood : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
  (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)

include hTateComparison

theorem albanese_identity_of_neighbors (t : TateComparison.Local.IntegralType s)
    (ht : ∀ (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
      (x : D.GeometricPoint b), D.neighbors t b x = {x}) : A.TAlb t = 1 := by
  apply AlbaneseExt.Construction.albanese_end_eq_one_of_differences D hgeometry
  intro k _ _ b j x y
  rw [hTateComparison.pointPush, ht k b, ht k b]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  rfl

theorem albanese_identity_of_natCentralMap
    (a : Fin s → ℕ) (h : ℕ) (ha : ∀ v, a v ≤ h)
    (hm : Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha = 1) :
    A.TAlb (Automorphisms.Construction.natCentralType a h ha) = 1 := by
  apply albanese_identity_of_neighbors D hgeometry hgood hIsogenyQuotient A hTateComparison
  intro k _ _ b x
  rw [Composition.Construction.centralModuliMap_neighbors D hgeometry hIsogenyQuotient hTateComparison.flags
    (Automorphisms.Construction.natCentralType a h ha) (fun v => a v) (fun _ _ => rfl)]
  change {x ≫ Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha} = {x}
  rw [hm]
  simp

theorem rho_natCentral_isOfFinOrder
    (hdegree : Module.finrank ℚ E = 2 * s) (hFiniteness : Arithmetic.Construction.PrincipalizationInput E)
    (a : Fin s → ℕ) (h : ℕ) (ha : ∀ v, a v ≤ h) :
    IsOfFinOrder (A.rho (CentralRepresentatives.Construction.centralCoset s q (fun v => a v) h)) := by
  obtain ⟨n, hn, hm⟩ :=
    (PoweredSideFinite.Construction.natCentralMap_isOfFinOrder D hgeometry hgood hIsogenyQuotient A hTateComparison hdegree hFiniteness a h ha).exists_pow_eq_one
  let u := Automorphisms.Construction.natCentralType (fun v => a v * n) (h * n) (fun v => Nat.mul_le_mul_right n (ha v))
  have hm' : Automorphisms.Construction.natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun v => a v * n) (h * n)
      (fun v => Nat.mul_le_mul_right n (ha v)) = 1 :=
    (Automorphisms.Construction.natCentralMap_pow D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha n).symm.trans hm
  have hu : A.TAlb u = 1 :=
    albanese_identity_of_natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison _ _ _ hm'
  have hρ : A.rho (CentralRepresentatives.Construction.centralCoset s q (fun v => (a v * n : ℕ)) (h * n : ℕ)) = 1 := by
    rw [CentralRepresentatives.Construction.centralCoset_eq_basis s q A.basis hTateComparison.raw]
    change A.rho (A.basis u.val) = 1
    rw [← hTateComparison.integral u, hu, map_one]
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hn, ?_⟩
  rw [← map_pow, centralCoset_pow]
  simpa only [Nat.cast_mul] using hρ

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseFinite.Construction
