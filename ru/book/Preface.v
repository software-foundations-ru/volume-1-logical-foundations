(** * Предисловие *)

(* #################################################################*)

(** * Приветствие! *)

(** Здесь начинается серия электронных книг "Основы программного
 обеспечения", описывающая математический фундамент, необходимый для
 создания надежных программ. Серия книг рассматривает такие темы как
 базовые понятия логики, доказательство теорем с помощью компьютера,
 инструмент интерактивного доказательства теорем Coq, функциональное
 программирование, логика рассуждений при построении программ,
 статические системы типов, property-based тестирование, и некоторые
 приемы для доказательства корректности кода на языке C. Предлагаемый
 материал предназначен для широкой аудитории читателей: от
 любопытствующих студентов до исследователей и ученых. Для чтения
 книги не требуется предварительных знаний в логике или практического
 опыта программирования, однако некоторый опыт в математических
 дисциплинах определенно будет полезен.

    Принципиальная новизна этой серии книг в том, что она на сто
    процентов формализована и проверена компьютером: каждый фрагмент
    текста - это по сути код для Coq. Книги предназначены для чтения
    совместно с (или прямо в) интерактивной сессией Coq. Весь текст и
    большинство упражнений придуманы так, что бы c ними можно было
    работать в Coq.

    Каждая книга представляет собой набор основных глав, охватывающих
    примерно семестр материала и организованных в форме линейного
    повествования, плюс некоторое колличество рекоммендуемых к
    изучению глав, покрывающих дополнительные темы. Предполагается что
    материал, изложенный во всех основных главах, доступен для
    понимания и для старшекурсников, и для выпускников.

    Книга которую вы сейчас читаете, называется "Основы логики", и
    является фундаментом для остальных книг в серии. Она знакомит
    читателя с базовыми идеями функционального программирования,
    конструктивной логики и инструмента интерактивного доказательства
    теорем Coq. *)

(* ################################################################# *)

(** * Обзор *)

    (** Создание надежного программного обеспечения - это тяжелая
    задача, крайне тяжелая. Масштабы и сложность современных систем,
    число людей, вовлеченных в их создание, а так же диапазон
    требований, накладываемых на эти системы, позволяет в лучшем
    случае создавать "более-менее" корректные системы, что довольно
    далеко от систем, корректных на 100%%. В то же время, постоянно
    увеличивающееся колличество перерабатываемой информации и ее
    влияние на каждый аспект жизни современного общества, значительно
    увеличивает цену от наличия ошибки или уязвимости.  Computer
    Science ученые и инженеры-программисты отвечают на эти вызовы
    выработкой множества техник для повышения надежности программ: от
    рекоммендаций по менеджменту команд разрабочиков (напр. методики
    экстремального программирования), до философии дизайна библиотек
    (напр. model-view-controller, publish-subscribe, и т.д.) и языков
    программирования (напр. объектно-ориентированное программирование,
    аспектно-ориентированное программирование, функциональное
    программирование, ...), до математических техник для определения
    свойств программного обеспечения, и инструментов помогающих их
    проверить. Серия книг "Основы программного обеспечения"
    фокусируется как-раз на этих инструментах.

    Этот том серии охватывает следующие три темы:

    (1) Основные логические инстрменты, позволяющие для составлять
    точные требования к программам.

    (2) Использование инструментов интерактивного доказательства
    теорем для построения строгих доказательств.

    (3) Функциональное программирование, как в качестве парадигмы
    программирования, которая делает понятнее рассуждения о
    программах, так и как связующий мост между программированием (как
    инженерной дисциплиной) и логикой (как наукой). *)

(* ================================================================= *)

(** ** Логика *)

(** Логика - это сфера науки, объектом изучения которой являются
    доказательства - неопровержимые свидетельства истинности
    каких-либо утверждений.  Большое колличество книг было написано о
    центральной роли логики в Сomputer Science дисциплинах. Manna и
    Waldinger называли её "алгебра computer science," тогда как
    Halpern в своей работе "On the Unusual Effectiveness of Logic in
    Computer Science" составил обширный список идей из логики, которые
    могут стать важными инструментами и открытиями для будущего
    специалиста. Так же он отмечает что "Оказалось, что логика имеет
    значительно больший эффект в computer science, чем до этого имела
    в математике. Это весьма примечательно, особенно если учесть тот
    факт, что последние сто лет логика наиболее активно развивалась
    как-раз математиками".

    В частности, фундаментальные инструменты индуктивных доказательств
    проникли во все сферы computer science. Вы определенно встречали
    их раньше, возможно в курсе по дискретной математике или анализу
    алгоритмов. Однако в этом курсе мы рассмотрим их значительно
    глубже, чем вы, вероятно, делали до сих пор. *)

(* =================================================================*)

(** ** Инструменты интерактивного доказательства теорем (Proof Assistants) *)

(** Заимствование идей между логикой и computer sciense не всегда
    направлено в одну сторону: развитие computer sciense так же
    произвело значительный вклад в логику.  Одним из примеров является
    разработка программных инструментов, которые помогают
    конструировать доказательства логических высказываний. Существует
    два основных типа таких инструментов:

       - Автоматические доказыватели теорем (automated theorem
        provers) позволяют выполнить следующую операцию "по нажатии
        одной кнопки": вы подаете на вход логическое высказывание, и
        затем программа возвращает вам ответ - "истина" или
        "ложь". Иногда результат высказывания остается неизвестен, так
        как вычисление результата высказывания не успевает закончиться
        за разумное время.  Несмотря на то, что возможности таких
        инструментов все ещё сильно огранченны довольно узкими
        областями применения, за последние годы виден значительный
        прогресс в качестве их работы.

       - Инструменты интерактивного доказательства теорем (proof
         assistants) - гибридные инструменты, который автоматизируют
         наиболее рутинные аспекты построение доказательств, но в
         более сложных аспектах полагаются на помощь со стороны
         человека. Популярными программами этого типа являются:
         Isabelle, Agda, Twelf, ACL2, PVS, Coq, и другие.

    Этот курс основан на Coq, инструменте интерактивного доказательства
    теорем, находящемся в разработке с 1983-го года. За последние годы
    Coq собрал крупное сообщество пользователей, состоящего как из людей
    занимающихся исследовательской деятельностью, так и из индустрии. Coq
    представляет собой богатую возможностями среду для интерактивной
    разработки формального доказательства и его автоматической проверки
    машиной. Ядром системы Coq, является простой доказыватель теорем,
    который всегда обеспечивает единственно верную последовательность
    шагов вывода. Поверх этого ядра Coq предоставляет удобные
    высокоуровневые возможности для разработки доказательств, включая
    обширную библиотеку распространенных определений и лемм, мощные
    так называемые тактики для конструирования сложных доказательств в
    полу-автоматическом режиме, а так же специальный язык
    программирования для написания новых тактик для более частных
    случаев.

    TODOCoq сыграл большую роль для большого количества работ в областях computer sciense и математики:

    - В качестве платформы моделирования языков программированиия, Coq
      стал одним из стандартных инструментом для исследователей,
      которым нужно описывать и обосновывать сложные языковые
      конструкции. Он использовался что бы удостовериться в
      защищенности платформы JavaCard, для получения сертификатов
      безопасности Common Criteria самого высокого уровня, для
      формализации спецификаций набора инструкций x86 и LLVM, а так же
      стандарта языка C.

    - В качестве среды для разработки формально верифицированного
      программного и аппаратного обеспечения, Coq применялся что бы
      разработать CompCert - полностью формально проверенный
      компилятор языка C, полностью формально верифицированный
      гипервизор CertiKOS, для доказательства корректности некоторых
      каверзных алгоритмов, включая многие для работы с числами с
      плавающей запятой, как основа CertiCrypt - набора инструментов
      для построения доказательств в области криптографии. Так же Coq
      использовался что бы сконструировать верифицированные реализации
      открытой (open-source) процессорной архитектуры с RISC-V.

    - As a _realistic environment for functional programming with
      dependent types_, it has inspired numerous innovations.  For
      example, the Ynot system embeds "relational Hoare reasoning" (an
      extension of the _Hoare Logic_ we will see later in this course)
      in Coq.

    - As a _proof assistant for higher-order logic_, it has been used
      to validate a number of important results in mathematics.  For
      example, its ability to include complex computations inside
      proofs made it possible to develop the first formally verified
      proof of the 4-color theorem.  This proof had previously been
      controversial among mathematicians because it required checking
      a large number of configurations using a program. In the Coq
      formalization, everything is checked, including the correctness
      of the computational part.  More recently, an even more massive
      effort led to a Coq formalization of the Feit-Thompson Theorem,
      the first major step in the classification of finite simple
      groups.

   By the way, in case you're wondering about the name, here's what
   the official Coq web site at INRIA (the French national research
   lab where Coq has mostly been developed) says about it: "Some
   French computer scientists have a tradition of naming their
   software as animal species: Caml, Elan, Foc or Phox are examples of
   this tacit convention. In French, 'coq' means rooster, and it
   sounds like the initials of the Calculus of Constructions (CoC) on
   which it is based."  The rooster is also the national symbol of
   France, and C-o-q are the first three letters of the name of
   Thierry Coquand, one of Coq's early developers. *)

(* ================================================================= *)
(** ** Functional Programming *)

(** The term _functional programming_ refers both to a collection of
    programming idioms that can be used in almost any programming
    language and to a family of programming languages designed to
    emphasize these idioms, including Haskell, OCaml, Standard ML,
    F##, Scala, Scheme, Racket, Common Lisp, Clojure, Erlang, and Coq.

    Functional programming has been developed over many decades --
    indeed, its roots go back to Church's lambda-calculus, which was
    invented in the 1930s, well _before_ the first electronic
    computers!  But since the early '90s it has enjoyed a surge of
    interest among industrial engineers and language designers,
    playing a key role in high-value systems at companies like Jane
    Street Capital, Microsoft, Facebook, Twitter, and Ericsson.

    The most basic tenet of functional programming is that, as much as
    possible, computation should be _pure_, in the sense that the only
    effect of execution should be to produce a result: it should be
    free from _side effects_ such as I/O, assignments to mutable
    variables, redirecting pointers, etc.  For example, whereas an
    _imperative_ sorting function might take a list of numbers and
    rearrange its pointers to put the list in order, a pure sorting
    function would take the original list and return a _new_ list
    containing the same numbers in sorted order.

    A significant benefit of this style of programming is that it
    makes programs easier to understand and reason about.  If every
    operation on a data structure yields a new data structure, leaving
    the old one intact, then there is no need to worry about how that
    structure is being shared and whether a change by one part of the
    program might break an invariant relied on by another part of the
    program.  These considerations are particularly critical in
    concurrent systems, where every piece of mutable state that is
    shared between threads is a potential source of pernicious bugs.
    Indeed, a large part of the recent interest in functional
    programming in industry is due to its simpler behavior in the
    presence of concurrency.

    Another reason for the current excitement about functional
    programming is related to the first: functional programs are often
    much easier to parallelize and physically distribute than their
    imperative counterparts.  If running a computation has no effect
    other than producing a result, then it does not matter _where_ it
    is run.  Similarly, if a data structure is never modified
    destructively, then it can be copied freely, across cores or
    across the network.  Indeed, the "Map-Reduce" idiom, which lies at
    the heart of massively distributed query processors like Hadoop
    and is used by Google to index the entire web is a classic example
    of functional programming.

    For purposes of this course, functional programming has yet
    another significant attraction: it serves as a bridge between
    logic and computer science.  Indeed, Coq itself can be viewed as a
    combination of a small but extremely expressive functional
    programming language plus a set of tools for stating and proving
    logical assertions.  Moreover, when we come to look more closely,
    we find that these two sides of Coq are actually aspects of the
    very same underlying machinery -- i.e., _proofs are programs_.  *)

(* ================================================================= *)
(** ** Further Reading *)

(** This text is intended to be self contained, but readers looking
    for a deeper treatment of particular topics will find some
    suggestions for further reading in the [Postscript] chapter.
    Bibliographic information for all cited works can be found in the
    file [Bib].*)

(* ################################################################# *)
(** * Practicalities *)

(* ================================================================= *)
(** ** System Requirements *)

(** Coq runs on Windows, Linux, and macOS.  You will need:

    - A current installation of Coq, available from the Coq home page.
      These files have been tested with Coq 8.12.

    - An IDE for interacting with Coq.  Currently, there are two
      choices:

        - Proof General is an Emacs-based IDE.  It tends to be
          preferred by users who are already comfortable with Emacs.
          It requires a separate installation (google "Proof
          General").

          Adventurous users of Coq within Emacs may want to check
          out extensions such as [company-coq] and [control-lock].

        - CoqIDE is a simpler stand-alone IDE.  It is distributed with
          Coq, so it should be available once you have Coq installed.
          It can also be compiled from scratch, but on some platforms
          this may involve installing additional packages for GUI
          libraries and such.

          Users who like CoqIDE should consider running it with the
          "asynchronous" and "error resilience" modes disabled:

              coqide -async-proofs off \
                     -async-proofs-command-error-resilience off Foo.v &
*)

(* ================================================================= *)
(** ** Exercises *)

(** Each chapter includes numerous exercises.  Each is marked with a
    "star rating," which can be interpreted as follows:

       - One star: easy exercises that underscore points in the text
         and that, for most readers, should take only a minute or two.
         Get in the habit of working these as you reach them.

       - Two stars: straightforward exercises (five or ten minutes).

       - Three stars: exercises requiring a bit of thought (ten
         minutes to half an hour).

       - Four and five stars: more difficult exercises (half an hour
         and up).

    Those using SF in a classroom setting should note that the autograder
    assigns extra points to harder exercises:

      1 star  = 1 point
      2 stars = 2 points
      3 stars = 3 points
      4 stars = 6 points
      5 stars = 10 points

    Some exercises are marked "advanced," and some are marked
    "optional."  Doing just the non-optional, non-advanced exercises
    should provide good coverage of the core material.  Optional
    exercises provide a bit of extra practice with key concepts and
    introduce secondary themes that may be of interest to some
    readers.  Advanced exercises are for readers who want an extra
    challenge and a deeper cut at the material.

    _Please do not post solutions to the exercises in a public place_.
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  We especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines. *)

(* ================================================================= *)
(** ** Downloading the Coq Files *)

(** A tar file containing the full sources for the "release version"
    of this book (as a collection of Coq scripts and HTML files) is
    available at https://softwarefoundations.cis.upenn.edu.

    If you are using the book as part of a class, your professor may
    give you access to a locally modified version of the files; you
    should use that one instead of the public release version, so that
    you get any local updates during the semester. *)

(* ================================================================= *)
(** ** Chapter Dependencies *)

(** A diagram of the dependencies between chapters and some suggested
    paths through the material can be found in the file [deps.html]. *)

(* ================================================================= *)
(** ** Recommended Citation Format *)

(** If you want to refer to this volume in your own writing, please
    do so as follows:

   @book            {$FIRSTAUTHOR:SF$VOLUMENUMBER,
   author       =   {$AUTHORS},
   title        =   "$VOLUMENAME",
   series       =   "Software Foundations",
   volume       =   "$VOLUMENUMBER",
   year         =   "$VOLUMEYEAR",
   publisher    =   "Electronic textbook",
   note         =   {Version $VERSION, \URLhttp://softwarefoundations.cis.upenn.edu },
   }
*)

(* ################################################################# *)
(** * Resources *)

(* ================================================================= *)
(** ** Sample Exams *)

(** A large compendium of exams from many offerings of
    CIS500 ("Software Foundations") at the University of Pennsylvania
    can be found at
    https://www.seas.upenn.edu/~cis500/current/exams/index.html.
    There has been some drift of notations over the years, but most of
    the problems are still relevant to the current text. *)

(* ================================================================= *)
(** ** Lecture Videos *)

(** Lectures for two intensive summer courses based on _Logical
    Foundations_ (part of the DeepSpec summer school series) can be
    found at https://deepspec.org/event/dsss17 and
    https://deepspec.org/event/dsss18/.  The video quality in the
    2017 lectures is poor at the beginning but gets better in the
    later lectures. *)

(* ################################################################# *)
(** * Note for Instructors *)

(** If you plan to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!

    In order to keep the legalities simple and to have a single point
    of responsibility in case the need should ever arise to adjust the
    license terms, sublicense, etc., we ask all contributors (i.e.,
    everyone with access to the developers' repository) to assign
    copyright in their contributions to the appropriate "author of
    record," as follows:

      - I hereby assign copyright in my past and future contributions
        to the Software Foundations project to the Author of Record of
        each volume or component, to be licensed under the same terms
        as the rest of Software Foundations.  I understand that, at
        present, the Authors of Record are as follows: For Volumes 1
        and 2, known until 2016 as "Software Foundations" and from
        2016 as (respectively) "Logical Foundations" and "Programming
        Foundations," and for Volume 4, "QuickChick: Property-Based
        Testing in Coq," the Author of Record is Benjamin C. Pierce.
        For Volume 3, "Verified Functional Algorithms", the Author of
        Record is Andrew W. Appel. For components outside of
        designated volumes (e.g., typesetting and grading tools and
        other software infrastructure), the Author of Record is
        Benjamin Pierce.

    To get started, please send an email to Benjamin Pierce,
    describing yourself and how you plan to use the materials and
    including (1) the above copyright transfer text and (2) your
    github username.

    We'll set you up with access to the git repository and developers'
    mailing lists.  In the repository you'll find a file [INSTRUCTORS]
    with further instructions. *)

(* ################################################################# *)
(** * Translations *)

(** Thanks to the efforts of a team of volunteer translators,
    _Software Foundations_ can be enjoyed in Japanese at
    http://proofcafe.org/sf.  A Chinese translation is also underway;
    you can preview it at https://coq-zh.github.io/SF-zh/. *)

(* ################################################################# *)
(** * Thanks *)

(** Development of the _Software Foundations_ series has been
    supported, in part, by the National Science Foundation under the
    NSF Expeditions grant 1521523, _The Science of Deep
    Specification_. *)

(* 2020-09-09 20:51 *)
