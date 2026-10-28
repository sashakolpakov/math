import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveCech

/-! # Quasicoherent Additive Cech -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.QuasicoherentAdditiveCech.Construction

noncomputable section

/-! The affine quasicoherent cocycle theorem after forgetting scalar multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

variable (R : CommRingCat.{u})

abbrev moduleSheafToAbelian (X : TopCat.{u}) : ModuleSheafInjectives.Construction.ModuleSheaves R X ⥤
    CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

theorem additiveAffine_exact_of_localizing
    (F : ModuleSheafInjectives.Construction.ModuleSheaves R (TopCat.of (PrimeSpectrum R))) (hF : IsLocalizing (R := R) F)
    {ι : Type v} [Fintype ι] [DecidableEq ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Exact
      (AdditiveCech.Construction.additiveAffineD0 R ((moduleSheafToAbelian R _).obj F) f)
      (AdditiveCech.Construction.additiveAffineD1 R ((moduleSheafToAbelian R _).obj F) f) := by
  change Function.Exact (AffineCech.Construction.affineCechD0 R F f) (AffineCech.Construction.affineCechD1 R F f)
  exact AffineCech.Construction.affineCech_exact_degreeOne R F hF f hf

theorem quasicoherent_additiveAffine_exact (N : (Spec R).Modules) [N.IsQuasicoherent]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Exact
      (AdditiveCech.Construction.additiveAffineD0 R ((moduleSheafToAbelian R _).obj (modulesSpecToSheaf.obj N)) f)
      (AdditiveCech.Construction.additiveAffineD1 R ((moduleSheafToAbelian R _).obj (modulesSpecToSheaf.obj N)) f) := by
  apply additiveAffine_exact_of_localizing R _ _ f hf
  exact (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.QuasicoherentAdditiveCech.Construction
