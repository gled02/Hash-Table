# Hash-Table

Fonctionnalités

Types utilisés :
    type couleur = Rouge | Noir | DoubleNoir
    
    type 'a arbre = Vide | VideNoir | Noeud of('a * couleur * 'a arbre * 'a arbre)
    
    type valeur = C.valeur
    
    type hashValToKey = (C.clef * valeur arbre) arbre
    
Avec C = le foncteur CoupleHashMap
Nous avons utilisé un arbre polymorphe afin de factoriser le code le plus possible.

TableDeHachage.ml : On part d’un module CoupleHashMap donné pour construire
une table de hachage. Et donc on définit une interface TableDeHachage et on crée un
foncteur de CoupleHashMap vers TabeDeHachage. Au final le foncteur
MakeTableDeHachage génère une table de hachage dont le fonctionnement équivaut
à celle du deuxième exercice du projet. On a généraliser les types en utilisant une
extension stockant un type (ordonné) valeur « hashé » sur un type (ordonné) « clef »,
utilisant une fonction « hash ».

HashStringToInt.ml : C’est un module pour clef = int et valeur = string. On n’utilise
pas de foncteur, donc ce n’est pas une généralissation.

Exemple.ml : C’est un exemple pour pouvoir executer notre code avec clef = int et
valeur = string.
