import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechSource

/-! # Section Cech Isomorphic Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechIsomorphicSource

noncomputable section

/-! Open Čech detection respects a genuine natural isomorphism of
global-section functors, including the canonical Ext-zero presentation. -/

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
  {K L : CochainComplex A ℕ} (f : K ⟶ L)
  {M : CochainComplex B ℕ} (s : M ⟶ (E.mapHomologicalComplex (.up ℕ)).obj K)

local notation "e'" => NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)

def globalSource := s ≫ (e').hom.app K

def cone := SectionCechSource.cone F G r K M (globalSource E F e s)

variable (hsource : QuasiIso (Presheaf.ConeQuasiIso.map U (cone E F G e r s)))
  (hmap : QuasiIso (SectionCechNaturality.map G U f))
  (hedge : QuasiIso (SectionCechNaturality.edge F G r U L))

include hsource hmap hedge in
omit [Finite ι] in
theorem quasiIso : QuasiIso (s ≫ (E.mapHomologicalComplex (.up ℕ)).map f) := by
  have hs := SectionCechSource.quasiIso F G r U K M (globalSource E F e s) hsource
  have hg := SectionCechNaturality.quasiIso F G r U f (globalSource E F e s)
    hs hmap hedge
  have heq : globalSource E F e s ≫ (F.mapHomologicalComplex (.up ℕ)).map f =
      (s ≫ (E.mapHomologicalComplex (.up ℕ)).map f) ≫ (e').hom.app L :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => s ≫ t) ((e').hom.naturality f).symm).trans
        (Category.assoc _ _ _).symm)
  apply (quasiIso_iff_comp_right _ ((e').app L).hom).mp
  exact heq ▸ hg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechIsomorphicSource
