import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterDetection

/-! # Line Character Independence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence.Construction.KernelCharacters

noncomputable section

/-!
# CartierDuality: kernel characters are independent of line-bundle presentations

The scalar comes from the actual descent isomorphism. Isomorphic line
bundles give the same scalar for every choice of pullback trivialization.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- Structure-module endomorphisms commute because they are global scalars. -/
theorem structureModuleEnd_comm (T : Scheme.{u}) (a b : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T)) :
    a ≫ b = b ≫ a := by
  apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective T
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (b * a) = AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (a * b)
  rw [map_mul, map_mul, mul_comm]

/-- Changing frames by the same invertible scalar at both endpoints
does not change the scalar of a compatible gluing map. -/
theorem framed_map_eq {C : Type*} [Category C] {U M₁ M₂ N₁ N₂ : C}
    (hc : ∀ a b : End U, a ≫ b = b ≫ a)
    (e₁ : M₁ ≅ U) (e₂ : M₂ ≅ U) (d₁ : N₁ ≅ U) (d₂ : N₂ ≅ U)
    (b₁ : M₁ ≅ N₁) (b₂ : M₂ ≅ N₂) (a : M₁ ⟶ M₂) (c : N₁ ⟶ N₂)
    (hb : b₁.hom ≫ c = a ≫ b₂.hom)
    (hr : e₁.inv ≫ b₁.hom ≫ d₁.hom = e₂.inv ≫ b₂.hom ≫ d₂.hom) :
    e₁.inv ≫ a ≫ e₂.hom = d₁.inv ≫ c ≫ d₂.hom := by
  let r : End U := e₂.inv ≫ b₂.hom ≫ d₂.hom
  have : IsIso r := by dsimp [r]; infer_instance
  apply (cancel_mono r).mp
  calc
    (e₁.inv ≫ a ≫ e₂.hom) ≫ r = e₁.inv ≫ a ≫ b₂.hom ≫ d₂.hom := by
      simp only [r, Category.assoc, Iso.hom_inv_id_assoc]
    _ = e₁.inv ≫ b₁.hom ≫ c ≫ d₂.hom := by rw [← Category.assoc a, ← hb, Category.assoc]
    _ = (e₁.inv ≫ b₁.hom ≫ d₁.hom) ≫ (d₁.inv ≫ c ≫ d₂.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = r ≫ (d₁.inv ≫ c ≫ d₂.hom) := by rw [hr]
    _ = (d₁.inv ≫ c ≫ d₂.hom) ≫ r := hc _ _

/-- The change between two pulled-back frames is the pullback of the
actual change-of-frame endomorphism. -/
theorem pulledFrame_change {X T : Scheme.{u}} {L M : X.Modules}
    (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (b : L ⟶ M) (x : T ⟶ X) :
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x).inv ≫ (Scheme.Modules.pullback x).map b ≫
        (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d x).hom = Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback x (e.inv ≫ b ≫ d.hom) := by
  simp only [Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback, Functor.map_comp, Category.assoc]

/-- Native canonical descent is natural in the original module morphism. -/
theorem canonicalDescent_naturality {X Y T : Scheme.{u}} (f : X ⟶ Y)
    {L M : Y.Modules} (b : L ⟶ M) (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullback x).map ((Scheme.Modules.pullback f).map b) ≫
        (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M).hom q x y hx hy =
      (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L).hom q x y hx hy ≫
        (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback f).map b) := by
  let Cx := Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx
  let Cy := Scheme.Modules.pullbackComp y f ≪≫ Scheme.Modules.pullbackCongr hy
  have hn : (Scheme.Modules.pullback x).map ((Scheme.Modules.pullback f).map b) ≫ Cx.hom.app M =
      Cx.hom.app L ≫ (Scheme.Modules.pullback q).map b := Cx.hom.naturality b
  have hm : (Scheme.Modules.pullback q).map b ≫ Cy.inv.app M =
      Cy.inv.app L ≫ (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback f).map b) :=
    Cy.inv.naturality b
  rw [Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom, Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom]
  change (Scheme.Modules.pullback x).map ((Scheme.Modules.pullback f).map b) ≫
    (Cx.hom.app M ≫ Cy.inv.app M) =
      (Cx.hom.app L ≫ Cy.inv.app L) ≫
        (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback f).map b)
  calc
    _ = Cx.hom.app L ≫ (Scheme.Modules.pullback q).map b ≫ Cy.inv.app M := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = _ := by rw [hm, Category.assoc]

/-- Equal pullbacks of global functions give equal pullbacks of their
structure-module endomorphisms. -/
theorem unitEndPullback_eq_of_same_base {S X T : Scheme.{u}} (p : X ⟶ S)
    (hp : Function.Surjective p.appTop) (x y : T ⟶ X) (hxy : x ≫ p = y ≫ p)
    (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) : Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback x a = Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback y a := by
  apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective T
  rw [Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback_scalar, Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback_scalar]
  obtain ⟨r, hr⟩ := hp (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X a)
  rw [← hr]
  exact congrArg (fun f : T ⟶ S => f.appTop r) hxy

/-- Compatible line-bundle presentations have exactly the same descent
scalar whenever functions on the source come from the common base. -/
theorem canonicalScalar_eq_of_lineIso
    {S X Y T : Scheme.{u}} (p : X ⟶ S) (hp : Function.Surjective p.appTop) (f : X ⟶ Y)
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (b : L.sheaf ≅ M.sheaf)
    (e : (Scheme.Modules.pullback f).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (d : (Scheme.Modules.pullback f).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (hxy : x ≫ p = y ≫ p) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf) e q x y hx hy =
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf) d q x y hx hy := by
  apply congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T)
  apply framed_map_eq (structureModuleEnd_comm T)
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e y)
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d x) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d y)
    ((Scheme.Modules.pullback x).mapIso ((Scheme.Modules.pullback f).mapIso b))
    ((Scheme.Modules.pullback y).mapIso ((Scheme.Modules.pullback f).mapIso b))
    _ _ (canonicalDescent_naturality f b.hom q x y hx hy)
  exact (pulledFrame_change e d ((Scheme.Modules.pullback f).map b.hom) x).trans
    ((unitEndPullback_eq_of_same_base p hp x y hxy _).trans
      (pulledFrame_change e d ((Scheme.Modules.pullback f).map b.hom) y).symm)

/-- An explicit native formula for the actual kernel scalar avoids
unfolding the entire descent object when making comparisons. -/
theorem lineKernelScalar_formula {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) :
    (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L e).kernelScalar =
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf) e
        ((1 : Picard.Homomorphisms.Kernel.Construction.kernelScheme f ⟶ A) ≫ f).left (1 : Picard.Homomorphisms.Kernel.Construction.kernelScheme f ⟶ A).left
        ((1 : Picard.Homomorphisms.Kernel.Construction.kernelScheme f ⟶ A) * (𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).left rfl
        (congrArg Over.Hom.left (Picard.Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f 1 (𝟙 _))) := rfl

variable {k : Type u} [Field k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- Isomorphic actual line bundles give identical kernel scalars,
independently of the chosen trivializations. -/
theorem lineKernelScalar_eq_of_iso (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (b : L.sheaf ≅ M.sheaf)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (d : (Scheme.Modules.pullback f.left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) :
    (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L e).kernelScalar =
      (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f M d).kernelScalar := by
  have : IsIso A.hom.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso A
  have hp := (ConcreteCategory.bijective_of_isIso A.hom.appTop).surjective
  let x : Picard.Homomorphisms.Kernel.Construction.kernelScheme f ⟶ A := 1
  let y : Picard.Homomorphisms.Kernel.Construction.kernelScheme f ⟶ A := x * (𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)
  have hs := canonicalScalar_eq_of_lineIso A.hom hp f.left L M b e d (x ≫ f).left x.left y.left rfl
    (congrArg Over.Hom.left (Picard.Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x (𝟙 _)))
    ((Over.w x).trans (Over.w y).symm)
  exact (lineKernelScalar_formula f L e).trans (hs.trans (lineKernelScalar_formula f M d).symm)

/-- The Hopf-coordinate character depends only on the actual original
line-bundle isomorphism class, and on no choice of frame. -/
theorem lineKernelCharacter_eq_of_iso (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (b : L.sheaf ≅ M.sheaf)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (d : (Scheme.Modules.pullback f.left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    [IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left] (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (.op R)).X ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) [IsMonHom i] :
    Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter L e R i = Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter M d R i := by
  apply GroupLike.ext
  exact congrArg (fun r => (Scheme.ΓSpecIso (.of R)).hom (i.left.appTop r))
    (lineKernelScalar_eq_of_iso f L M b e d)

/-- The actual character attached to a class in the pullback kernel.
The computation theorem below makes its independence of all choices explicit. -/
def pullbackClassCharacter [IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left] (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (.op R)).X ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) [IsMonHom i]
    (q : {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left}) : GroupLike k R :=
  Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter (Classical.choose (LineCharacterDetection.Construction.KernelCharacters.exists_trivialized_representative f q))
    (Classical.choice (Classical.choose_spec (LineCharacterDetection.Construction.KernelCharacters.exists_trivialized_representative f q)).2) R i

/-- The class character can be computed using any representative and
any actual trivialization of its pullback. -/
theorem pullbackClassCharacter_eq [IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left] (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (.op R)).X ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) [IsMonHom i]
    (q : {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left})
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = q.val)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) :
    pullbackClassCharacter f R i q = Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter L e R i := by
  let M := Classical.choose (LineCharacterDetection.Construction.KernelCharacters.exists_trivialized_representative f q)
  have hM : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M = q.val ∧
      Nonempty ((Scheme.Modules.pullback f.left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) :=
    Classical.choose_spec (LineCharacterDetection.Construction.KernelCharacters.exists_trivialized_representative f q)
  have b : Nonempty (M.sheaf ≅ L.sheaf) := Quotient.exact (hM.1.trans hL.symm)
  exact lineKernelCharacter_eq_of_iso f M L b.some hM.2.some e R i

/-- The canonical character distinguishes actual line-bundle classes
when the native group morphism is a faithfully flat cover. -/
theorem pullbackClassCharacter_injective [IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (R : CommHopfAlgCat k)
    (i : ((hopfSpec (.of k)).obj (.op R)).X ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) [IsMonHom i.hom] :
    Function.Injective (pullbackClassCharacter f R i.hom) := by
  intro q r h
  obtain ⟨L, hL, ⟨e⟩⟩ := LineCharacterDetection.Construction.KernelCharacters.exists_trivialized_representative f q
  obtain ⟨M, hM, ⟨d⟩⟩ := LineCharacterDetection.Construction.KernelCharacters.exists_trivialized_representative f r
  have hc : Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter L e R i.hom = Picard.Homomorphisms.LineKernelCharacters.Construction.lineKernelCoordinateCharacter M d R i.hom :=
    (pullbackClassCharacter_eq f R i.hom q L hL e).symm.trans
      (h.trans (pullbackClassCharacter_eq f R i.hom r M hM d))
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M :=
    Quotient.sound (LineCharacterDetection.Construction.KernelCharacters.line_iso_of_character_eq f L M e d R i hc)
  exact Subtype.ext (hL.symm.trans (he.trans hM))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence.Construction.KernelCharacters
