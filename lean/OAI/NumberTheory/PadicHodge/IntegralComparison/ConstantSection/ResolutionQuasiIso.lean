import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechIsomorphicResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexPostcompose

/-! # Resolution Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ResolutionQuasiIso

noncomputable section

/-! Canonical constant-sheaf sections compute an injective target when
their genuine open Čech cone, target map, and injective edge are
quasi-isomorphisms. All comparison cancellations precede specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z r s
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  {D : Type r} [Category.{s} D] [HasBinaryProducts D]
  (F : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{max w z} R) [F.Additive]
  (G : Sheaf J (ModuleCat.{w} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max w z} R) [G.Additive]
  (e : Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0 ≅ F)
  (b : F ⋙ Functor.const Dᵒᵖ ⟶ G)
  {ι : Type} [Finite ι] (U : ι → D)
  (M : CochainComplex (ModuleCat.{w} R) ℕ)
  {K K' I : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ}
  (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).obj M ⟶ K')
  (t : K ≅ K') (f : K ⟶ I)

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections.constantUnit R J) 0

variable (hsource : QuasiIso (Presheaf.ConeQuasiIso.map U
    (OpenTotal.sectionMap.{u,v,w,z,r,s} R J F G e.hom b M K' a)))
  (hmap : QuasiIso ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((G.mapHomologicalComplex (.up ℕ)).map f))))
  (hedge : QuasiIso (Presheaf.ConeQuasiIso.map (A := ModuleCat.{max w z} R) U
    (M := (F.mapHomologicalComplex (.up ℕ)).obj I)
    ((b.mapHomologicalComplex (.up ℕ)).app I)))

/-- Constant sections followed by the original map through the resolving complex. -/
def resolvedMap := ComplexMap.map R J M K' a ≫
  ((E).mapHomologicalComplex (.up ℕ)).map (t.inv ≫ f)

private abbrev resolvedMap_quasiIso :=
  Open.SectionCechIsomorphicResolution.quasiIso E F G e b U t f
    (ComplexMap.map R J M K' a) hsource hmap hedge

include hsource hmap hedge in
omit [Finite ι] in
theorem quasiIso : QuasiIso
    (ComplexMap.map.{u,v,w,z} R J M I (a ≫ t.inv ≫ f)) := by
  exact ComplexPostcompose.quasiIso R J M a (t.inv ≫ f)
    (resolvedMap_quasiIso R J F G e b U M a t f hsource hmap hedge)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ResolutionQuasiIso
