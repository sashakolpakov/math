import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechIsomorphicSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CechMapQuasiIso

/-! # Section Cech Isomorphic Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechIsomorphicResolution

noncomputable section

/-! Open Čech detection after changing the resolving sheaf complex by
an actual isomorphism. The functorial cancellation is performed before
specializing any crystalline complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A]
  {B : Type a} [Category.{b} B] [Abelian B]
  [HasProducts.{0} B] [HasCoproducts.{0} B]
  (E F : A ⥤ B) [E.Additive] [F.Additive]
  (G : A ⥤ Cᵒᵖ ⥤ B) [G.Additive]
  (e : E ≅ F) (r : F ⋙ Functor.const Cᵒᵖ ⟶ G)
  {ι : Type} [Finite ι] (U : ι → C)
  {K K' I : CochainComplex A ℕ} (t : K ≅ K') (f : K ⟶ I)
  {M : CochainComplex B ℕ} (s : M ⟶ (E.mapHomologicalComplex (.up ℕ)).obj K')
  (hsource : QuasiIso (Presheaf.ConeQuasiIso.map U
    (SectionCechIsomorphicSource.cone E F G e r s)))
  (hmap : QuasiIso ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((G.mapHomologicalComplex (.up ℕ)).map f))))
  (hedge : QuasiIso (Presheaf.ConeQuasiIso.map (A := B) U
    (M := (F.mapHomologicalComplex (.up ℕ)).obj I)
    ((r.mapHomologicalComplex (.up ℕ)).app I)))

include hsource hmap hedge in
omit [Finite ι] in
theorem quasiIso : QuasiIso (s ≫ (E.mapHomologicalComplex (.up ℕ)).map (t.inv ≫ f)) :=
  SectionCechIsomorphicSource.quasiIso E F G e r U (t.inv ≫ f) s hsource
    (CechMapQuasiIso.Section.quasiIso_of_map G U t f hmap) hedge

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechIsomorphicResolution
