import OAI.NumberTheory.PadicHodge.IntegralComparison.TerminalModuleProjective

/-! # Disjoint Cover Module Projective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DisjointCoverModuleProjective

noncomputable section

/-! Disjoint covers by objects with split covering sieves make global module sections exact. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R]

theorem empty_zero (F : Sheaf J (ModuleCat.{w} R)) (W : C) (hW : (⊥ : Sieve W) ∈ J W) :
    IsZero (F.obj.obj (op W)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply F.property.hom_ext ⟨⊥, hW⟩
  rintro ⟨V, f, hf⟩
  exact False.elim hf

def sectionHom (M : ModuleCat.{w} R) (x : M) : ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

variable {ι : Type z} {T : C} (U : ι → C) (f : ∀ i, U i ⟶ T) [∀ i, Mono (f i)]
  (hcover : Sieve.ofArrows U f ∈ J T)
  (hdisjoint : ∀ {W : C} {i j : ι}, i ≠ j →
    ∀ (a : W ⟶ U i) (b : W ⟶ U j), a ≫ f i = b ≫ f j → (⊥ : Sieve W) ∈ J W)

include hdisjoint in
theorem compatible (F : Sheaf J (ModuleCat.{w} R))
    {E : ModuleCat.{w} R} (x : ∀ i, E ⟶ F.obj.obj (op (U i)))
    {W : C} {i j : ι} (a : W ⟶ U i) (b : W ⟶ U j) (h : a ≫ f i = b ≫ f j) :
    x i ≫ F.obj.map a.op = x j ≫ F.obj.map b.op := by
  by_cases hij : i = j
  · subst j
    rw [(cancel_mono (f i)).mp h]
  · exact (empty_zero J R F W (hdisjoint hij a b h)).eq_of_tgt _ _

include hcover hdisjoint in
theorem glue (F : Sheaf J (ModuleCat.{w} R)) (x : ∀ i, F.obj.obj (op (U i))) :
    ∃ y : F.obj.obj (op T), ∀ i, F.obj.map (f i).op y = x i := by
  obtain ⟨g, hg, _⟩ := F.property.existsUnique_amalgamation_ofArrows f hcover
    (fun i => sectionHom R _ (x i))
    (fun {W} {i} {j} a b h => compatible J R U f hdisjoint F (fun i => sectionHom R _ (x i)) a b h)
  refine ⟨g 1, fun i => ?_⟩
  have hi := congrArg (fun q : ModuleCat.of R R ⟶ F.obj.obj (op (U i)) => q 1) (hg i)
  change F.obj.map (f i).op (g 1) = (1 : R) • x i at hi
  exact hi.trans (one_smul R (x i))

include hcover in
omit [∀ i, Mono (f i)] in
theorem separated (F : Sheaf J (ModuleCat.{w} R)) (x y : F.obj.obj (op T))
    (h : ∀ i, F.obj.map (f i).op x = F.obj.map (f i).op y) : x = y := by
  have hxy : sectionHom R _ x = sectionHom R _ y := by
    apply F.property.hom_ext_ofArrows f hcover
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change F.obj.map (f i).op (r • x) = F.obj.map (f i).op (r • y)
    rw [map_smul, map_smul, h i]
  have hh := congrArg (fun q : ModuleCat.of R R ⟶ F.obj.obj (op T) => q 1) hxy
  change (1 : R) • x = (1 : R) • y at hh
  simpa only [one_smul] using hh

variable [HasSheafify J (ModuleCat.{w} R)]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  (hsplit : ∀ i, ∀ S : Sieve (U i), S ∈ J (U i) → S = ⊤)

include hcover hdisjoint hsplit in
theorem epi_surjective {F G : Sheaf J (ModuleCat.{w} R)} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op T)) := by
  intro x
  choose y hy using fun i => TerminalModuleProjective.epi_surjective J R (hsplit i) φ
    (G.obj.map (f i).op x)
  obtain ⟨s, hs⟩ := glue J R U f hcover hdisjoint F y
  refine ⟨s, separated J R U f hcover G _ x (fun i => ?_)⟩
  have h := congrArg (fun q : F.obj.obj (op T) ⟶ G.obj.obj (op (U i)) => q s)
    (φ.hom.naturality (f i).op)
  change φ.hom.app (op (U i)) (F.obj.map (f i).op s) = G.obj.map (f i).op (φ.hom.app (op T) s) at h
  exact h.symm.trans ((congrArg (φ.hom.app (op (U i))) (hs i)).trans (hy i))

include hcover hdisjoint hsplit in
theorem projective (hterminal : IsTerminal T) :
    Projective ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)) := by
  have : ((sheafSections J (ModuleCat.{w} R)).obj (op T)).PreservesEpimorphisms :=
    ⟨fun φ _ => ConcreteCategory.epi_of_surjective _ (epi_surjective J R U f hcover hdisjoint hsplit φ)⟩
  exact (constantSheafAdj J (ModuleCat.{w} R) hterminal).map_projective _ inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DisjointCoverModuleProjective
