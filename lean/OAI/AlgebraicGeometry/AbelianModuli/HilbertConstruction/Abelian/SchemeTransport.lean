import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Scheme Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Transport an abelian scheme structure along an actual isomorphism over its base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ}

/-- Commutativity is retained by the transported group structure. -/
theorem SchemeTransport.transported_group_commutative (A : Schemes.AbelianScheme g S) {Z : Over S}
    (e : A.scheme ≅ Z) :
    letI := GrpObj.ofIso e
    IsCommMonObj Z := by
  let := GrpObj.ofIso e
  constructor
  change (β_ Z Z).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ μ[A.scheme] ≫ e.hom) =
    (e.inv ⊗ₘ e.inv) ≫ μ[A.scheme] ≫ e.hom
  rw [← Category.assoc, ← braiding_naturality, Category.assoc, IsCommMonObj.mul_comm_assoc]

/-- An isomorphic scheme over the same base carries the transported abelian structure. -/
def Schemes.AbelianScheme.transport (A : Schemes.AbelianScheme g S) {Z : Over S} (e : A.scheme ≅ Z) :
    Schemes.AbelianScheme g S := by
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).map e.inv))
  have h : IsPullback e.inv.left Z.hom A.scheme.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨e.inv.w.trans (Category.comp_id _).symm⟩
  exact
    { scheme := Z
      group := GrpObj.ofIso e
      commutative := SchemeTransport.transported_group_commutative A e
      proper := MorphismProperty.of_isPullback (P := @IsProper) h A.proper
      smoothDimension := (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
        h A.smoothDimension
      connected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h A.connected }

/-- The original isomorphism identifies the original and transported group schemes. -/
def Schemes.AbelianScheme.transportIso (A : Schemes.AbelianScheme g S) {Z : Over S} (e : A.scheme ≅ Z) :
    A.scheme ≅ (A.transport e).scheme := e

instance Schemes.AbelianScheme.transportIso_preservesGroup (A : Schemes.AbelianScheme g S) {Z : Over S}
    (e : A.scheme ≅ Z) : IsMonHom (A.transportIso e).hom :=
  isMonHom_ofIso e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
