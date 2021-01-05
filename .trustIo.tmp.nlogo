;directed-link-breed [  Dlinks Dlink]
;Dlinks-own[
;  feedback_weight ; total sum of feedbacks between 2 peers
;  No_malicious_transaction_between_src_dest
;  total_transaction_between_src_dest
;  local_trust_ ; Normalized local trust between 2 peers
;]

globals[
  time
  total_global_transactions ;  the global number of transactions
  number_of_nodes;
  current_ticks;
  trust_checkpoint; ;ticks where the system updates the trust
  number_of_malicous_nodes
  number_of_good_nodes
  security_treshold ; to vote trust score should be > security_treshold
  successful_transactions;
  malicious_transactions
  Gamma ; convergence treshold
error_rate ; error rate
s_rate; success rate

]
;globals variables hold values that are accessible anywhere in th program
;link parameters
links-own [
  feedback_weight ; total sum of feedbacks between 2 peers
  correct_feedback_weight; total of real feedbacks
  No_malicious_transaction_between_src_dest
  total_transaction_between_src_dest
  local_trust_ ; Normalized local trust between 2 peers
  correct_local_trust_; used to  RMS

]
;;peer's parameters
turtles-own [

  service               ;;each node offer a certian number of services, we will use just 0 or 1
  peer_total_transactions    ;;N of tx performed by the peer
  ;peer_trust_value        ;;peers label
  malicious             ;;is the peer malicious or not?

  list_other_peer_id ; a list of peers that the peers rated
  list_in_peer_id ; a list of peers that rated the current peer

  global_trust_value; GT(P)

  correct_global_trust_value; GT' used in RMS error computation
  trust_score; T(P)
  total_Local_trust
  old_GT
  old__correct_GT
  user_behaviour
  device_security
  number_of_iterations
  pertinence_ratio;
]


to setup
  settings-initialization
  clear-all                       ;; clear everything on canvas
  setup-nodes                     ;; a procedure to set nodes
  ;setup-edges                     ;; a procedure to set edges
  setup-malicious-nodes
  ;ask turtles [ set color red]   ;; paint nodes red
  ask links [set color white]     ;; paint edges white
  reset-ticks
  layout
end
;--------------------------------------
;Network intialization
;-------------------------------------
to setup-nodes
  set-default-shape turtles "circle"
  set number_of_nodes number_of_peers ;number_peers is defined in the interface
  create-turtles number_of_nodes
  ask turtles
  [
    set color green
    set size 1.2

    ;;set service
    ifelse random_service
    [set service random 2];no_services_available ;either it provides the service or not !!2not1
    [set service 1]
    ;;initialise the initial trust values
    set global_trust_value global_initial_trust_value
    set correct_global_trust_value global_initial_trust_value
    ;set trust_score global_initial_trust_value
    set number_of_iterations 0
    ;;set the label for the nodes
    set label precision global_trust_value 3 ;1.25 2 digits after .
    set pertinence_ratio 0
    ;;set malicious status
    set malicious false

    ; for visual reasons, we don't put any nodes *too* close to the edges
    ;setxy (random-xcor * 0.95) (random-ycor * 0.95)

    initialize-turtle-lists self; initialize turtles lists and vars
    let x random-float 1
    set device_security round (100 - secrurity% )/ 100
    let y random-float 1
    set user_behaviour  round (100 - user_behaviour% )/ 100

    set  trust_score alpha * global_trust_value * user_behaviour + beta * device_security

  ]



end

to setup-malicious-nodes
    ;;set malicious peers according to percentage
  let n_malicious round ((number_of_nodes * prctge_of_malicious_nodes) / 100) ; malicious_peers % defined in the interface

  let malicious_peers_set n-of n_malicious turtles
  ask malicious_peers_set
  [
    set color red
    set malicious true
  ]


  ;;calculate number of malicous nodes in the network
  set number_of_malicous_nodes n_malicious
  ;;calculate number of good nodes
  set number_of_good_nodes number_of_nodes - number_of_malicous_nodes
  show word "number of malicious peers :" number_of_malicous_nodes
end



to setup-edges
  let num-links  6

  while [ count links < num-links ] ;; num-links given by the user from interface
  [
    ask one-of turtles
    [
      let other_turtle one-of other turtles

      if other_turtle != nobody [ create-link-to other_turtle ]
      ask out-link-to other_turtle [
        set feedback_weight 10
        ;set label feedback_weight

      ]
      show word " new link:" out-link-to other_turtle
      ask out-link-to other_turtle[
          if feedback_weight = 0 ; for unkonw reason weight for some links isn't set in the previous operation
          [
          show word "error weigh detected and corrected" other_turtle
          set feedback_weight 10

        ]
          show word "weight is" feedback_weight
      ]
    ]
  ]
    ; make the network look a little prettier
   ; repeat 10
    ;[
     ; layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ;]
end


;--------------------------------------
; Initialition and entrypoint
;-------------------------------------
to settings-initialization
  set security_treshold 0.2
  set Gamma 0.00001 ; to modify treshold of confergence
  set malicious_transactions 0
  set successful_transactions 0
end

to initialize-turtle-lists [peer]
  ;;initialise feedback lists
  set list_other_peer_id []
  set list_in_peer_id []
  set trust_checkpoint 0
end


to go

  if not any? turtles [stop] ;exits if there are no more turtles
  set current_ticks ticks
  set time current_ticks
  show "---------------------------------"
  show word "the current tick " current_ticks
  show "---------------------------------"
  ask turtles [; reinitialization
  set number_of_iterations 0
  let degree count my-in-links
    ifelse degree > 0
    [set pertinence_ratio trust_score / degree ]
    [set pertinence_ratio trust_score ]
  ]

  ifelse all_peers_transact [
    let sample 0
    ifelse all_or_sample[
    set sample number_of_peers
    ]
    [
     set sample random number_of_peers
    ]

    let peers_neighbours nobody

    ifelse remove_dangling_nodes[
      set peers_neighbours up-to-n-of number_of_peers turtles with [ count my-in-links = 0 and count my-out-links = 0]
      print( word "selected dangling neighbours " peers_neighbours count peers_neighbours )
      if count peers_neighbours = 0 [
        set peers_neighbours n-of sample turtles
        print( word "selected neighbours after no dangling " peers_neighbours count peers_neighbours )
        ]
    ]
    [
      if peers_neighbours = nobody [
        set peers_neighbours n-of sample turtles
      ]
    ]
    ask peers_neighbours  [
      all_transact self
     ]
  ]
  [
    ont_to_one_transact
  ] ; one peer transacts per tick

  ;let tick_checkpoint current_ticks mod update_trust_interval
  ;if update_trust_or_not and (tick_checkpoint = 0) [   ;update the trust in the network after update_trust_interval tick
  ;show word "------------------tick_checkpoint---------------" tick_checkpoint
  ;update_trust_with_total_trust
  ;set number_of_iterations 0
  update_trust_with_global_trust
  update_trust_with_correct_global_trust
  ;set trust_checkpoint tick_checkpoint
  ;]
  ;if current_ticks > 50  [clear-output]
  ;layout
  ;ask turtles [
  ;set total_Local_trust sum [local_trust_] of my-out-links
  ;print( word"--9999---  total local trust of " self "in others is " round total_Local_trust)
  ;]
  layout2
  tick
end

;--------------------------------------
; Functions
;-------------------------------------

to all_transact [peer1]
; peer1 will request a service from another peer


  if evaluate-connections [ ;=> this might disturb the calcul if the GT is not alreaady calculated as it will remove links between peers
   evaluate-current-connections peer1
    ]


   let potential_partners_list find-potential_peers-to-connect-with 1 [who] of peer1  ;nodes providing the service
    ;<========== Already sorted by trust_score
    ;set sorted_list sort-on [(- trust_score)] potential_peers
    ;let potential_partners_sorted_pertinence sort-on [(- trust_score )] potential_partners_list
    print (word "==> potential_partners_list of" peer1 " are " potential_partners_list )
    ;;check if there are items in the list
    let peer2 0 ; will host the other peer who provides the service

    ;set sorted_list sort-on [(- trust_score)] potential_peers
    ;;select a random peer
   ifelse order_by_pertinence_ratio[
      let tset turtle-set potential_partners_list;
      let sorted_ratio_list sort-on [( - pertinence_ratio)] tset;
    ;turtle-set
      set peer2 item 0 sorted_ratio_list;
  ]
  [    ifelse choose_random_or_most_trusted ; if true => random if not =>most trusted
    [
      set peer2 item random (length potential_partners_list) potential_partners_list
    ]
    [
      set peer2 item 0 potential_partners_list ;;set the chosen peer to the most trusted peer
    ]
  ]
      ;;final check
      if [who] of peer1 = [who] of peer2
      [
        stop ;;exit the procedure
        show " ERROR!!!!!! exiting for equality reason"
      ]


    ;;perform the transaction between two peers
  ifelse malicious_transactions_percentage = 0
    [perform-transaction-and-rate peer1 peer2]    ;peer2 send tx to peer1 and get feedback freom it
    [perform-transaction-and-rate_with_probability peer1 peer2 ]
    ;compute-global-trust peer2
end


to ont_to_one_transact
; peer1 will request a service from another peer
  let peer1 nobody
  ifelse remove_dangling_nodes[
  set peer1 one-of turtles with [ count my-in-links = 0 and count my-out-links = 0]
    if peer1 = nobody [show "no more dangling nodes" set peer1 one-of turtles]
    ]

  [set peer1 one-of turtles]

  if evaluate-connections [ ;=> this might disturb the calcul if the GT is not alreaady calculated as it will remove links between peers
   evaluate-current-connections peer1
    ]


   let potential_partners_list find-potential_peers-to-connect-with 1 [who] of peer1  ;nodes providing the service

   print (word "==> potential_partners_list of" peer1 " are " potential_partners_list )

    ;;check if there are items in the list
    let peer2 0 ; will host the other peer who provides the service

    ifelse length potential_partners_list < 1
    [
      stop ;;exit the procedure
    ]
    [
      ;;select a random peer
    ifelse choose_random_or_most_trusted ; defined in the interface => choose most ranked node or at random
    [
      set peer2 item random (length potential_partners_list) potential_partners_list
    ]
    [
      set peer2 item 0 potential_partners_list ;;set the chosen peer to the most trusted peer
    ]

      ;;final check
      if [who] of peer1 = [who] of peer2
      [
        stop ;;exit the procedure
        show " ERROR!!!!!! exiting for equality reason"
      ]
    ]

    ;;perform the transaction between two peers
    perform-transaction-and-rate peer1 peer2    ;peer2 send tx to peer1 and get feedback freom it

    ;compute-global-trust peer2
end

;not mine
;;evaluates all the connections of a peer
;;the link is removed if the nodes trust value is below the threshold
to evaluate-current-connections [peer]

  if not [malicious] of peer[
    ask peer
  [
      show "die peer evaluation"
    ask my-out-links ;the agentset containing all links
    [
      if [global_trust_value] of other-end < trust_threshold
      [
        die ; ceases to exist
        show word "a linnk died to out" other-end
      ]
    ]

   ask my-in-links ;the agentset containing all links
    [
      if [global_trust_value] of other-end < trust_threshold
      [
        die ; ceases to exist
        show word "a linnk died from in" other-end
      ]
    ]
  ]
]
end

;Not mine
;;finding peers who offer the desired service
;;returns a list of the top [no_peers_to_return] peers
to-report find-potential_peers-to-connect-with [required-service peerid] ; required-service is a parameter, the number of possible services is defined in the interface ==> here the random walk should be performed

  let potential_peers []
  ifelse malicious_gives_only_feedback
  [
    set potential_peers other turtles with [service = required-service and who != peerid and (count my-in-links <= max_in_links) and trust_score > trust_threshold and malicious = false ] ; select new neighbours with specific conditions
  ]
  [
    set potential_peers other turtles with [service = required-service and who != peerid and (count my-in-links <= max_in_links) and trust_score > trust_threshold   ] ; select new neighbours with specific conditions
  ]
    ;print( word "the list of potential peeers with specific values  service" required-service "for the peer" peerid  )

  if  count potential_peers = 0 [ ; use this cached list if no new nodes are available
    print( word "-----count potential_peers = 0")
    ask turtle peerid [
      set potential_peers out-link-neighbors
  ]]

  print( word "the list of potential peeers is " potential_peers "for the peer" peerid)
  let no_peers_to_return  number_peers_to_return
  let sorted_list 0
  ;;return number of peers
  ifelse count potential_peers >= no_peers_to_return ;;list is small than number that needs to be returned
  [
    ;;sort the list and return only the first [no_peers_to_return]
    ;set sorted_list sublist ( sort-on [( - global_trust_value)] potential_peers ) 0 no_peers_to_return
    set sorted_list sublist ( sort-on [( - trust_score)] potential_peers ) 0 no_peers_to_return
  ]
  [
    ;;sort the entire list
   ; set sorted_list sort-on [(- global_trust_value)] potential_peers
    set sorted_list sort-on [(- trust_score)] potential_peers
  ]
print( word "the list sorted_list is " sorted_list)
  report sorted_list
end


to perform-transaction-and-rate_with_probability [peer1 peer2]   ; Transaction is from peer2 to peer1


  let peer1_id [who] of peer1 ; destination
  let peer2_id [who] of peer2 ; source

  ;;get the exact time of the transaction
  let time_of_transaction current_ticks
  let rand random 100

  let peer2_act_maliciously false

  if [malicious] of peer2 ;;this peer is malicious ; it gives only malicious tx
    [
    if rand < malicious_transactions_percentage ; % defined by interface and < 100
     [
      set peer2_act_maliciously true
    ]
    ]


  ;;perform actions via peer1
  ask turtle peer1_id
  [
   print (word "==> peer " peer1 "requests tx from" peer2 )
   ;;update origional peer (peer1) feedback history based on the feedback from peer2



      ifelse peer2_act_maliciously     [ ;peer 2 is malicious

      ifelse not [malicious] of peer1 [ ;peer1 not malicious => peer2 malicious
        setup-feedback_edges_between peer1 peer2 -1 -1
        set malicious_transactions malicious_transactions + 1
        print( word "the given feedback setup-feedback_edges_between peer1 peer2 -1 -1")
      ]
      [ ;peer1 is malicious

        ifelse rand < malicious_feedback_percentage [ ;peer1  malicious => peer2  malicious
        setup-feedback_edges_between peer1 peer2 1 -1
        set successful_transactions successful_transactions + 1
         print( word "the given feedback setup-feedback_edges_between peer1 peer2 1 -1")
        ]

        [setup-feedback_edges_between peer1 peer2 -1 -1
        set malicious_transactions malicious_transactions + 1
        print( word "the given feedback  setup-feedback_edges_between peer1 peer2 -1 -1")
        ]

      ]

    ]
    [ ;peer 2 is honnest

        ifelse not [malicious] of peer1 [ ;peer1 not malicious peer 2 is honnest
        setup-feedback_edges_between peer1 peer2 1 1
        set successful_transactions successful_transactions + 1
        print (word "x setup-feedback_edges_between peer1 peer2 1 1")
      ]
      [;peer1 malicious feedback inversed
        ;peer1 malicious
         ifelse rand < malicious_feedback_percentage [  ;peer1 malicious peer 2 is honnest
         setup-feedback_edges_between peer1 peer2 -1 1
         set malicious_transactions malicious_transactions + 1
         print (word "setup-feedback_edges_between peer1 peer2 -1 1")
       ]
        [;peer1 not malicious peer 2 is honnest
          setup-feedback_edges_between peer1 peer2 1 1
        set successful_transactions successful_transactions + 1
        print (word "x setup-feedback_edges_between peer1 peer2 1 1")
        ]

    ]
    ]


     ask out-link-to peer2 [
       if peer2_act_maliciously
      [
          if not [malicious] of peer1
        [
        ;print( word "acts maliciously" peer2)
        set No_malicious_transaction_between_src_dest No_malicious_transaction_between_src_dest + 1 ; one more malicious tx
        print (word "No_malicious_transaction_between_src_dest in incremented even (peer1 not malicious) and new value is " No_malicious_transaction_between_src_dest)
        ]

      ]
      set total_transaction_between_src_dest total_transaction_between_src_dest + 1

    ]

    compute-local-trust peer1 peer2
    compute-correct-local-trust peer1 peer2

set peer_total_transactions peer_total_transactions + 1

   ]


  set total_global_transactions total_global_transactions + 1
end




;;this method performs the transaction part of a collaboration
to perform-transaction-and-rate [peer1 peer2]   ; Transaction is from peer2 to peer1

  ;;get the id of origional node
  let peer1_id [who] of peer1 ; destination
  ;;get the id of other node
  let peer2_id [who] of peer2 ; source

  ;;get the exact time of the transaction
  let time_of_transaction current_ticks


  ;;determing if any of the peers will act maliciously during this transaction
  ;let peer1_act_maliciously true
  let peer2_act_maliciously false

  if [malicious] of peer2 ;;this peer is malicious ; it gives only malicious tx
    [
       set peer2_act_maliciously true
     ]


  ;;perform actions via peer1
  ask turtle peer1_id
  [
   print (word "==> peer " peer1 "requests tx from" peer2 )

    ifelse peer2_act_maliciously     [ ;peer 2 is malicious

      ifelse not [malicious] of peer1 [ ;peer1 not malicious => peer2 malicious
        setup-feedback_edges_between peer1 peer2 -1 -1
        set malicious_transactions malicious_transactions + 1
        print( word "the given feedback setup-feedback_edges_between peer1 peer2 -1 -1")
      ]
      [ ;peer1 is malicious

        setup-feedback_edges_between peer1 peer2 1 -1
        set malicious_transactions malicious_transactions + 1
          print( word "the given f   setup-feedback_edges_between peer1 peer2 1 -1")

      ]

    ]
    [ ;peer 2 is honnest

        ifelse not [malicious] of peer1 [ ;peer1 not malicious peer 2 is honnest
        setup-feedback_edges_between peer1 peer2 1 1
        set successful_transactions successful_transactions + 1
        print (word "x setup-feedback_edges_between peer1 peer2 1 1")
      ]
      [
          setup-feedback_edges_between peer1 peer2 -1 1
        set successful_transactions successful_transactions + 1

        print (word " setup-feedback_edges_between peer1 peer2 -1 1")


    ]
    ]


     ask out-link-to peer2 [
       if peer2_act_maliciously
      [
          if not [malicious] of peer1
        [
        ;print( word "acts maliciously" peer2)
        set No_malicious_transaction_between_src_dest No_malicious_transaction_between_src_dest + 1 ; one more malicious tx
        print (word "No_malicious_transaction_between_src_dest in incremented even (peer1 not malicious) and new value is " No_malicious_transaction_between_src_dest)
        ]

      ]
      set total_transaction_between_src_dest total_transaction_between_src_dest + 1

    ]

    compute-local-trust peer1 peer2
    compute-correct-local-trust peer1 peer2

set peer_total_transactions peer_total_transactions + 1

   ]


  set total_global_transactions total_global_transactions + 1
end



to setup-feedback_edges_between [peer1 peer2 feedback correctfeedback] ; P1 => P2


    ask peer1
    [
     let other_turtle peer2


     if other_turtle = nobody
     [stop]

      if out-link-to other_turtle = nobody ;or (not member? peer1 list_other_peer_id)  ; create new link if a DIRECT link P1=>p2 doesn't exist
      [
      create-link-to other_turtle
      show "======================================"
      show word " ==> new link:" out-link-to other_turtle
      show "======================================"
         ]


      ask out-link-to other_turtle [

        let original_feedback feedback_weight
      let original_correct_feedback_weight correct_feedback_weight
        set feedback_weight feedback_weight + feedback

      ;------------------for RMS -------------------------------
        set correct_feedback_weight correct_feedback_weight + correctfeedback
      ;------------------for RMS -------------------------------

          if feedback_weight = original_feedback ; for unkonw reason feedback_weight for some links isn't set in the previous operation
          [

          set feedback_weight feedback_weight + feedback

        ]

                if original_correct_feedback_weight = correct_feedback_weight ; for unkonw reason feedback_weight for some links isn't set in the previous operation
          [

          set correct_feedback_weight correct_feedback_weight + correctfeedback

        ]

      ]

        if  not member? other_turtle list_other_peer_id
        [set list_other_peer_id lput other_turtle list_other_peer_id
               ]

        ask other_turtle[
        if  not member? peer1 list_in_peer_id ;here
        [set list_in_peer_id lput peer1 list_in_peer_id]
        ]

    ]

    ; make the network look a little prettier
   ; repeat 10
   ; [
    ;  layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ;]

end

to compute-local-trust [peer1 peer2]  ;local trust that peer1 has in 2

  let sigma_tx 0 ; Sigma tx
  let sum_p_q 0 ; Sum(P,Q)
  let sigma_sum 0; Sigma sum
  let S 0 ; S(P,Q)
   ask peer1
  [
    ;print (word "list " peer1 "is" list_other_peer_id)

    ask my-out-links[
    print (word "123456 malicious tx number is " No_malicious_transaction_between_src_dest)
    let AR_p_q   (total_transaction_between_src_dest - No_malicious_transaction_between_src_dest) / total_transaction_between_src_dest
    if feedback_weight > 0 [set sum_p_q feedback_weight * AR_p_q]
    set sigma_sum sigma_sum + sum_p_q ; => in eigentrust they use  sigma max 0, s to avoid summing neg sum_p_q as they don't turn it to 0 if neg as we do
    ]


    ask out-link-to peer2[

    let AR_p_q   (total_transaction_between_src_dest - No_malicious_transaction_between_src_dest) / total_transaction_between_src_dest
    ifelse feedback_weight > 0 [
        set sum_p_q feedback_weight * AR_p_q
      ]
      [
          set sum_p_q 0

      ]

       ifelse sigma_sum != 0
      [
        ifelse sum_p_q > 0
        [set S sum_p_q / sigma_sum
          set  local_trust_ S
        ]
        [set  local_trust_ 0]
      ]
      [set  local_trust_ 0]


        set label precision local_trust_ 3
    ]

      ask my-out-links [ ;update other LT after the change of LT peer1=> peer2
      show word "old local trust" local_trust_
      let AR_p_q   (total_transaction_between_src_dest - No_malicious_transaction_between_src_dest) / total_transaction_between_src_dest
      ifelse feedback_weight > 0 [set sum_p_q feedback_weight * AR_p_q][set sum_p_q  0]

       ifelse sigma_sum != 0
      [ifelse sum_p_q > 0
        [set S sum_p_q / sigma_sum
          set  local_trust_ S
        ]
        [set  local_trust_ 0]
      ]
      [set  local_trust_ 0
      ]

        set label precision local_trust_ 3
    ]

  ]
end


to compute-correct-local-trust [peer1 peer2]  ;local trust that peer1 has in 2

  let sigma_tx 0 ; Sigma tx
  let sum_p_q 0 ; Sum(P,Q)
  let sigma_sum 0; Sigma sum
  let S 0 ; S(P,Q)
   ask peer1
  [
    ;print (word "list " peer1 "is" list_other_peer_id)

    ask my-out-links[
    print (word "N of malicious tx number is " No_malicious_transaction_between_src_dest)
    let AR_p_q   (total_transaction_between_src_dest - No_malicious_transaction_between_src_dest) / total_transaction_between_src_dest
    if correct_feedback_weight > 0 [set sum_p_q correct_feedback_weight * AR_p_q]
    set sigma_sum sigma_sum + sum_p_q ; => in eigentrust they use  sigma max 0, s to avoid summing neg sum_p_q as they don't turn it to 0 if neg as we do
    ]


    ask out-link-to peer2[

    let AR_p_q   (total_transaction_between_src_dest - No_malicious_transaction_between_src_dest) / total_transaction_between_src_dest
    ifelse correct_feedback_weight > 0 [
        set sum_p_q correct_feedback_weight * AR_p_q
      ]
      [
          set sum_p_q 0

      ]

       ifelse sigma_sum != 0
      [
        ifelse sum_p_q > 0
        [set S sum_p_q / sigma_sum
          set  correct_local_trust_ S
        ]
        [set  correct_local_trust_ 0]
      ]
      [set  correct_local_trust_ 0]


       ; set label precision local_trust_ 3
    ]

      ask my-out-links [ ;update other LT after the change of LT peer1=> peer2
      show word "old local correct_local_trust_" correct_local_trust_
      let AR_p_q   (total_transaction_between_src_dest - No_malicious_transaction_between_src_dest) / total_transaction_between_src_dest
      ifelse correct_feedback_weight > 0 [set sum_p_q correct_feedback_weight * AR_p_q][set sum_p_q  0]

       ifelse sigma_sum != 0
      [ifelse sum_p_q > 0
        [set S sum_p_q / sigma_sum
          set  correct_local_trust_ S
        ]
        [set  correct_local_trust_ 0]
      ]
      [set  correct_local_trust_ 0
      ]

    ]

  ]
end

 ;-------------------------------
;Global trust computation
;--------------------------------
to compute-global-trust [peer]

;let total_trust 0.0
show word "computing GT of " peer
ask peer
[
    let GT_P global_trust_value
    let GT_P' 0
    let in_links count my-in-links
 ; ask my-links ;the agentset containing all links
    let GTs []
    let sum_GT_P sum_global_trust  peer ;sum of GT of peers pointing to current peer
    print (word "====> pointing peers to " peer "are" list_in_peer_id "links  by asking"  in-link-neighbors "for sum" sum_GT_P )
if in_links >= feedback_treshold [ ; Update GT only if enough input links
   ask in-link-neighbors [

       ; set the GT of current peer
       let GT_i global_trust_value

        ask out-link-to peer [
        let local_trust_i local_trust_
        let v compute_logistic other-end
        if sum_GT_P > 0
        [
          let GT_P_i (local_trust_i * GT_i * v ) / (sum_GT_P)
        set GTs lput GT_P_i GTs
          ]
        ]

      ]

    ifelse length GTs > 0
    [
      set GT_P  sum GTs
      ;set GT_P global_initial_trust_value + sum GTs

    ]
    [set GT_P global_trust_value];if no in neighbors keep global_trust_value

    if GT_P > 1 ; sanity check
    [ print (word "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" GT_P "of" self) ]

    print (word "====> new GT of" peer "is " GT_P)
    set global_trust_value   GT_P

    set label precision global_trust_value  3
  ]
]


end

to compute-correct-global-trust [peer]

;let total_trust 0.0
show word "computing GT of " peer
ask peer
[
    let in_links count my-in-links
    let GT_P correct_global_trust_value
    let GT_P' 0
    let GTs []
    let sum_GT_P sum_correct_global_trust  peer ;sum of GT of peers pointing to current peer
if in_links >= feedback_treshold [ ; Update GT only if enough input links
   ask in-link-neighbors [

       ; set the GT of current peer
       let GT_i correct_global_trust_value

        ask out-link-to peer [
        let local_trust_i correct_local_trust_
        let v compute_logistic other-end
        if sum_GT_P > 0
        [
          let GT_P_i (local_trust_i * GT_i * v ) / (sum_GT_P)
        set GTs lput GT_P_i GTs
          ]
        ]

      ]

    ifelse length GTs > 0
    [
      set GT_P  sum GTs
    ]
    [
      set GT_P correct_global_trust_value
    ];if no in neighbors keep correct_global_trust_value

    print (word "====> new GT of correct GT" peer "is " GT_P)
    set correct_global_trust_value  GT_P
  ]
]


end

to-report compute_logistic [peer]
   let val 0
  ask peer[
  set  val 1 / ( 1 + exp( -  peer_total_transactions )) ; pivot after n tx
  ]
  report val
end

to-report sum_global_trust[ peer]
  let temp_sum 0
  ask peer[

 ;set old_GT sum [global_trust_value] of turtles ;
    ask in-link-neighbors [
     set temp_sum temp_sum + global_trust_value

    ]
  ]

report temp_sum
end


to-report sum_correct_global_trust[ peer]
  let temp_sum 0
  ask peer[

 ;set old_GT sum [global_trust_value] of turtles ;
    ask in-link-neighbors [
     set temp_sum temp_sum + correct_global_trust_value

    ]
  ]

report temp_sum
end

to-report globabl_trust_sum_all_peers ;used in output

let globabl_trust_sum_all_peers_ 0
;let tick_checkpoint current_ticks mod update_trust_interval

;if update_trust_or_not and (tick_checkpoint > 0)
;[
set globabl_trust_sum_all_peers_ sum [global_trust_value] of turtles
;]
report globabl_trust_sum_all_peers_
end



to-report sum_trust_score[ peer]
  let temp_sum 888
  ask peer[
    set temp_sum 0;trust_score
 ;set old_GT sum [global_trust_value] of turtles ;
    ask in-link-neighbors [

      set temp_sum temp_sum + trust_score


    ]


  ]
report temp_sum

end

;to update_trust_with_total_trust
;  show "=============================================== updating trust"


;  let new_GT sum [global_trust_value] of turtles ;

;  let old_sum_GT sum [global_trust_value] of turtles ;

;    ask turtles [ ; ask all peers
    ;set old_GT lput global_trust_value old_GT
;    print (word "global trust of " self "before is " global_trust_value)
    ;compute-global-trust self
;    compute-global-trust_score self
;    print (word "global trust of " self "after is " global_trust_value)
;      ]

;   set new_GT sum [global_trust_value] of turtles ;

  ;------- to activate
;   while [not convergence old_sum_GT new_GT ]
;;    [
;  set old_sum_GT new_GT
;  ask turtles [ ; ask all peers

    ;compute-global-trust self
;        compute-global-trust_score self

;  ]
;  set new_GT sum [global_trust_value] of turtles ;
;  print ( word "the convergence old_sum_GT" old_sum_GT "and new GT" new_GT)


;    ]
;  show "====================Successfull convergence==============================="
;end



to update_trust_with_global_trust
  show "=============================================== updating trust"

  ;let old_GT sum [global_trust_value] of turtles ;
  ;let new_GT old_GT


  let list_T_i []
  let list_T_i+1 []
    ask turtles [ ; ask all peers
    ;set old_GT lput global_trust_value old_GT

    print (word "global trust of " self "before is " global_trust_value)
    set list_T_i lput global_trust_value list_T_i
    set old_GT global_trust_value
    compute-global-trust self
    print (word "global trust of " self "after is " global_trust_value)
    set list_T_i+1 lput global_trust_value list_T_i+1
      ]

   ;set new_GT sum [global_trust_value] of turtles ;

  ask turtles with [ count my-in-links >= feedback_treshold] [ ;------- to activate
   while [not convergence old_GT global_trust_value ]
    [
    show word "inside while with inlinks" count my-in-links
    set old_GT global_trust_value

    compute-global-trust self

  print (word "old_GT " self  " " old_GT "global_trust_value is " global_trust_value)

  print ( word "the convergence old_GT" old_GT "and conv is " convergence old_GT global_trust_value)
  set number_of_iterations number_of_iterations + 1
    ]
   set  trust_score alpha * global_trust_value * user_behaviour + beta * device_security
   show word "trust_score" trust_score
]
  show "====================Successfull convergence==============================="


end



to update_trust_with_correct_global_trust
  show "=============================================== updating correct trust"

  ;let old_GT sum [global_trust_value] of turtles ;
  ;let new_GT old_GT


  let list_T_i []
  let list_T_i+1 []
    ask turtles [ ; ask all peers
    ;set old_GT lput global_trust_value old_GT
    ;print (word "correct_ trust of " self "before is " correct_global_trust_value)
    set list_T_i lput correct_global_trust_value list_T_i
    set old__correct_GT correct_global_trust_value
    compute-correct-global-trust self
    ;print (word "global trust of " self "after is " global_trust_value)
    set list_T_i+1 lput correct_global_trust_value list_T_i+1
      ]

   ;set new_GT sum [global_trust_value] of turtles ;

 ask turtles with [ count my-in-links >= feedback_treshold]  [
   while [not convergence old__correct_GT correct_global_trust_value ]
    [
    set old__correct_GT correct_global_trust_value
    compute-correct-global-trust self

    ]
   ;set  trust_score alpha * global_trust_value * user_behaviour + beta * device_security
   ;show word "trust_score" trust_score
]
  show "====================Successfull crct convergence==============================="


end

to-report convergence [GT GT']
let converge false
  if precision abs(GT' - GT) 6 <= Gamma
  [set converge true]
  show word "the difference is " abs(GT' - GT)
report converge

end
;----------------
;random walker
;------------------------
to walker
  ask turtles [
    forward 1        ;; all turtles move forward one step
    right random 360 ;; and turn a random amount
  ]
end


;--------------------------
;Plot
;------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;         PLOT        ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;this methods plots the points representing the trust computation error rate against the percentage of malicious peers
;;the parameter computation_type takes 0 for conventional or 1 for trust computation error rate
to trust-computation-error [computation_type]
  set error_rate 0

  ifelse computation_type = 0
  [
    set error_rate sum ([ global_trust_value * global_trust_value] of turtles)
  ]
  [
    ask turtles
    [
      ifelse malicious
      [
        set error_rate error_rate + (1 - (malicious_transactions / 100))
      ]
      [ ;not malicious
        set error_rate error_rate + 1
      ]
    ]
  ]

  set error_rate error_rate / count turtles
  ;;show word "trust computation error " precision (sqrt error_rate) 3
  ;;set trust_computation_error sqrt error_rate
  ;;set percentage_of_malicious_peers malicious_peers
end

to-report success_rate


ifelse total_global_transactions = 0 [set s_rate  0]
[set s_rate   successful_transactions / total_global_transactions]



plot  s_rate

end
to-report square [x]
  report x * x
end
;-------------------------------
;Display settings
;--------------------------------
to layout
    repeat 10
    [
      layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ]
end
to layout2
  ;; the number 3 here is arbitrary; more repetitions slows down the
  ;; model, but too few gives poor layouts
  repeat 3 [
    ;; the more turtles we have to fit into the same amount of space,
    ;; the smaller the inputs to layout-spring we'll need to use
    let factor sqrt count turtles
    ;; numbers here are arbitrarily chosen for pleasing appearance
    layout-spring turtles links (1 / factor) (7 / factor) (10 / factor)
    display  ;; for smooth animation
  ]
  ;; don't bump the edges of the world
  let x-offset max [xcor] of turtles + min [xcor] of turtles
  let y-offset max [ycor] of turtles + min [ycor] of turtles
  ;; big jumps look funny, so only adjust a little each time
  set x-offset limit-magnitude x-offset 0.1
  set y-offset limit-magnitude y-offset 0.1
  ask turtles [ setxy (xcor - x-offset / 2) (ycor - y-offset / 2) ]
end
to-report limit-magnitude [number limit]
  if number > limit [ report limit ]
  if number < (- limit) [ report (- limit) ]
  report number
end
