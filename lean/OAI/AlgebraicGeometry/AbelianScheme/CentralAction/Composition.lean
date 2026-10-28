import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PEL
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Separation
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Coefficients

/-! # Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Composition.Construction

noncomputable section

/-! The raw central multiplication identities determine the actual
correspondence composition. No geometric composition law is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem exponents_of_central_eq {t : TateComparison.Local.LocalType s} {a : Fin s → ℤ} {h : ℤ}
    (ht : t = CentralRepresentatives.Construction.centralType a h) : ∀ v i, t.exponent v i = a v := by
  intro v i
  rw [ht]
  rfl

theorem central_coefficients_eq_single
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
    (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)
    (u v w : TateComparison.Local.IntegralType s) (a b : Fin s → ℤ) (m n : ℤ)
    (hu : u.val = CentralRepresentatives.Construction.centralType a m) (hv : v.val = CentralRepresentatives.Construction.centralType b n)
    (hw : w.val = CentralRepresentatives.Construction.centralType (fun j => a j + b j) (m + n)) :
    A.coeff u v = Finsupp.single w 1 := by
  have hprod : A.basis w.val = A.basis u.val * A.basis v.val := by
    rw [hu, hv, hw, ← CentralRepresentatives.Construction.centralCoset_eq_basis s q A.basis hTateComparison.raw,
      ← CentralRepresentatives.Construction.centralCoset_eq_basis s q A.basis hTateComparison.raw,
      ← CentralRepresentatives.Construction.centralCoset_eq_basis s q A.basis hTateComparison.raw, CentralRepresentatives.Construction.centralCoset_mul]
  apply Coefficients.Construction.raw_expansion_single (TateComparison.HeckeKernel.integralLevel s q)
    (fun t : TateComparison.Local.IntegralType s => TateComparison.HeckeKernel.representative s q t.val)
    (fun t : TateComparison.Local.IntegralType s => A.basis t.val) (fun t => hTateComparison.raw t.val) w ?_
    (A.coeff u v) (hprod.trans (hTateComparison.coefficients u v))
  intro t ht
  apply Subtype.ext
  rw [hw]
  rw [hw, CentralRepresentatives.Construction.representative_centralType] at ht
  exact Separation.Construction.central_orbit_representative_unique s q t.val _ _ ht

theorem centralModuliMap_neighbors
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hflags : D.HasPolarizedFlagRealizations hIsogenyQuotient)
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x : D.GeometricPoint b) :
    D.neighbors t b x = {x ≫ PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hflags t a ha} := by
  have := PEL.Construction.central_correspondence_source_isIso D hgeometry hIsogenyQuotient hflags t a ha
  exact (D.correspondence t).neighbors_of_source_iso b x

/-- TateComparison's multiset convolution, with the proved coefficient one, gives
composition of the actual central scheme morphisms. -/
theorem centralModuliMap_comp
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
    (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)
    (u v w : TateComparison.Local.IntegralType s) (a b : Fin s → ℤ) (m n : ℤ)
    (hu : u.val = CentralRepresentatives.Construction.centralType a m) (hv : v.val = CentralRepresentatives.Construction.centralType b n)
    (hw : w.val = CentralRepresentatives.Construction.centralType (fun j => a j + b j) (m + n)) :
    PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags u a (exponents_of_central_eq hu) ≫
      PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags v b (exponents_of_central_eq hv) =
    PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags w (fun j => a j + b j)
      (exponents_of_central_eq hw) := by
  have : Smooth D.model.space.hom := hgeometry.smooth
  have : IsProper D.model.space.hom := hgeometry.proper
  have : Smooth D.space.hom := inferInstanceAs
    (Smooth (CategoryTheory.Limits.pullback.snd D.model.space.hom D.generic))
  have : IsProper D.space.hom := inferInstanceAs
    (IsProper (CategoryTheory.Limits.pullback.snd D.model.space.hom D.generic))
  have : IsReduced D.space.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.space.hom
  apply TateComparison.GeometricExt.over_hom_ext_geometric
  intro k _ _ base x
  have hc := hTateComparison.neighbors u v k base x
  rw [central_coefficients_eq_single D hgeometry hgood hIsogenyQuotient A hTateComparison u v w a b m n hu hv hw,
    Finsupp.sum_single_index] at hc
  · simp only [one_nsmul] at hc
    rw [centralModuliMap_neighbors D hgeometry hIsogenyQuotient hTateComparison.flags u a (exponents_of_central_eq hu),
      Multiset.singleton_bind,
      centralModuliMap_neighbors D hgeometry hIsogenyQuotient hTateComparison.flags v b (exponents_of_central_eq hv),
      centralModuliMap_neighbors D hgeometry hIsogenyQuotient hTateComparison.flags w (fun j => a j + b j)
        (exponents_of_central_eq hw)] at hc
    exact (Category.assoc _ _ _).symm.trans (Multiset.singleton_inj.mp hc)
  · simp

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Composition.Construction
