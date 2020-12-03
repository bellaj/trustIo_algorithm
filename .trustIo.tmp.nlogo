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
]
;globals variables hold values that are accessible anywhere in th program
;link parameters
links-own [
  feedback_weight ; total sum of feedbacks between 2 peers
  No_malicious_transaction_between_src_dest
  total_transaction_between_src_dest
  local_trust_ ; Normalized local trust between 2 peers
  
]
;;peer's parameters
turtles-own [
  security_score
  User_behavior
  service               ;;each node offer a certian number of services, we will use just 0 or 1
  peer_total_transactions    ;;N of tx performed by the peer
  ;peer_trust_value        ;;peers label
  malicious             ;;is the peer malicious or not?

  list_other_peer_id ; a list of peers that the peers rated
  list_in_peer_id ; a list of peers that rated the current peer

  global_trust_value; GT(P)
  trust_score; T(P)
  total_Local_trust
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
    set service random 2;no_services_available ;either it provides the service or not !!2not1

    ;;initialise the initial trust values
    set global_trust_value global_initial_trust_value
    set trust_score global_initial_trust_value

    ;;set the label for the nodes
    set label precision global_trust_value 2 ;1.25 2 digits after .


    ;;set malicious status
    set malicious false

    ; for visual reasons, we don't put any nodes *too* close to the edges
    ;setxy (random-xcor * 0.95) (random-ycor * 0.95)

    initialize-turtle-lists self; initialize turtles lists and vars
  ]



end

to setup-malicious-nodes
    ;;set malicious peers according to percentage
  let n_malicious round ((number_of_nodes * number_of_malicious_nodes) / 100) ; malicious_peers % defined in the interface

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
    repeat 10
    [
      layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ]
end


;--------------------------------------
; Initialition and entrypoint
;-------------------------------------
to settings-initialization
  set security_treshold 0.2
  set Gamma 0.01 ; to modify treshold of confergence
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
  show "---------------------------------"
  show word "the current tick " current_ticks
  show "---------------------------------"
  transact

  let tick_checkpoint round (current_ticks / 1000)

  if update_trust_or_not and (tick_checkpoint = trust_checkpoint + 1) [   ;update the trust in the network after 500 tick
  update_trust
  set trust_checkpoint tick_checkpoint

  ]
  ;layout
  ask turtles [
    set total_Local_trust sum [local_trust_] of my-out-links
    ;print( word"--9999---  total local trust of " self "in others is " round total_Local_trust)
  ]
  tick
end

;--------------------------------------
; Functions
;-------------------------------------
to transact

  let peer1 one-of turtles   ; will request a service from another peer


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
  ask peer
  [
    ask my-out-links ;the agentset containing all links
    [
      if [global_trust_value] of other-end < trust_threshold
      [
        die ; ceases to exist
      ]
    ]
  ]
end

;Not mine
;;finding peers who offer the desired service
;;returns a list of the top [no_peers_to_return] peers
to-report find-potential_peers-to-connect-with [required-service peerid] ; required-service is a parameter, the number of possible services is defined in the interface ==> here the random walk should be performed
  let potential_peers other turtles with [service = required-service and who != peerid ] ; add and trust_score > trust_treshold

  let no_peers_to_return  number_of_peers - 1
  let sorted_list 0
  ;;return number of peers
  ifelse count potential_peers >= no_peers_to_return ;;list is small than number that needs to be returned
  [
    ;;sort the list and return only the first [no_peers_to_return]
    set sorted_list sublist ( sort-on [( - global_trust_value)] potential_peers ) 0 no_peers_to_return
  ]
  [
    ;;sort the entire list
    set sorted_list sort-on [(- global_trust_value)] potential_peers
  ]

  report sorted_list
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
  let peer2_act_maliciously true

  if [malicious] of peer2 ;;this peer is malicious ; it gives only malicious tx
    [
    ;if random 101 <= malicious_transactions_percentage ; % defined by interface and < 100
    ; [
      set peer2_act_maliciously true
    ;]
    ]

 if not [malicious] of peer2 ;;this peer is malicious ;; IMO malicious peers can act or not maliciously
    [
      ifelse random 101 < malicious_transactions_percentage ; % defined by interface and < 100
      [    set peer2_act_maliciously true      ]
      [    set peer2_act_maliciously false     ]
    ]

  ;show word "=> peer2 will act (false) in case 0% set " peer2_act_maliciously

  ;;perform actions via peer1
  ask turtle peer1_id
  [
   print (word "==> peer " peer1 "requests tx from" peer2 )
   ;;update origional peer (peer1) feedback history based on the feedback from peer2

    ifelse peer2_act_maliciously     [ 
    setup-feedback_edges_between peer1 peer2 -1
    set malicious_transactions malicious_transactions + 1
    ]
    [ setup-feedback_edges_between peer1 peer2 1
    set successful_transactions successful_transactions + 1
    ]


     ask out-link-to peer2 [
       if peer2_act_maliciously
      [
        set No_malicious_transaction_between_src_dest No_malicious_transaction_between_src_dest + 1 ; one more malicious tx
      ]
      set total_transaction_between_src_dest total_transaction_between_src_dest + 1

    ]

    compute-local-trust peer1 peer2


set peer_total_transactions peer_total_transactions + 1

   ]


  set total_global_transactions total_global_transactions + 1
end



to setup-feedback_edges_between [peer1 peer2 feedback] ; P1 => P2


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
        set feedback_weight feedback_weight + feedback

          if feedback_weight = original_feedback ; for unkonw reason feedback_weight for some links isn't set in the previous operation
          [
          show word "error weigh detected and corrected" other_turtle
          set feedback_weight feedback_weight + feedback

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
    repeat 10
    [
      layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ]
end

to compute-local-trust [peer1 peer2]  ;local trust that peer1 has in 2

  let sum_feedback 0

   ask peer1
  [
    foreach list_other_peer_id
    [ ?1 ->
     ask out-link-to ?1 ;the agentset containing all links ( !!!!! ASK only outgoing links)
    [

    if feedback_weight > 0 [
    set sum_feedback sum_feedback + feedback_weight
     ]

    ]
    ]
  
    ;set sum_feedback sum [ feedback_weight > 0] of my-out-links
    print( word "7777 sum_feedback of "  peer1 "is" sum_feedback)
    ;if sum_feedback = 0
    ;[set sum_feedback  1]
    
    ask my-out-links[
      if total_transaction_between_src_dest > 0
      [
      let sum_p_q feedback_weight
      ifelse sum_p_q > 0 [
      
      let AR_p_q   (total_transaction_between_src_dest - No_malicious_transaction_between_src_dest) / total_transaction_between_src_dest
;!! case AR <0??,
      print (word " AR_p_q between" peer1 "=>" peer2 "is=" AR_p_q "and sum_p_q " sum_p_q)
      set sum_p_q sum_p_q * AR_p_q
      let LTR  precision  ((sum_p_q / sum_feedback) ) 2
      ;let LTR   ((sum_p_q / sum_feedback) ) 
      set  local_trust_ LTR

      ;show word "==>> local trust" local_trust_
      set label  local_trust_
        ]
        [
          set label 0
        ]
        
       print (word "00 Local trust between" peer1 "=>" peer2 "is=" local_trust_)
      ]
    ]
  ]
end

;-------------------------------
;Global trust computation
;--------------------------------
to compute-global-trust [peer]

let total_trust 0.0
show word "computing GT of " peer
ask peer
[
    let GT_P global_trust_value
    let GT_P' 0
 ; ask my-links ;the agentset containing all links
    let GTs []
    let sum_GT_P sum_global_trust  peer ;sum of GT of peers pointing to current peer
   print (word "====> pointing peers to " peer "are" list_in_peer_id)
   foreach list_in_peer_id
   [ ?1 ->
      ;if feedback_weight > 0 [ ]
      ;show  "computing GT of step1"
      ask  ?1 [

       ; set the GT of current peer
       let GT_i global_trust_value


       if out-link-to peer != nobody[
          ask out-link-to peer [
          ;show  "computing GT of step3"
        let local_trust_i local_trust_
        if sum_GT_P > 0
        [
        let GT_P_i (local_trust_i * GT_i) / (sum_GT_P)
        set GTs lput GT_P_i GTs
          ]
        ]
      ]
      ]
    ]

    if length GTs > 1 and (sum GTs > 0)
    [set GT_P sum GTs]

print (word "====> new GT of" peer "is " GT_P)

    set global_trust_value GT_P
    set label precision global_trust_value 2
]


end

to-report sum_global_trust[ peer]
  let temp_sum 888
  ask peer[
    set temp_sum global_trust_value
 ;set old_GT sum [global_trust_value] of turtles ;
   if length list_in_peer_id > 0
    [foreach list_in_peer_id
   [ ?1 ->

    ask ?1[

     set temp_sum temp_sum + global_trust_value
    ]

    ]
    ]


  ]
report temp_sum

end




to update_trust
  show "=============================================== updating trust"

  let old_GT global_initial_trust_value
  let new_GT global_initial_trust_value

  set old_GT sum [global_trust_value] of turtles ;

    ask turtles [ ; ask all peers
    ;set old_GT lput global_trust_value old_GT
    print (word "global trust of " self "before is " global_trust_value)
    compute-global-trust self
    print (word "global trust of " self "after is " global_trust_value)
      ]

   set new_GT sum [global_trust_value] of turtles ;

  ;------- to activate
   while [not convergence old_GT new_GT ]
    [
  set old_GT new_GT
  ask turtles [ ; ask all peers

    compute-global-trust self

  ]
  set new_GT sum [global_trust_value] of turtles ;
  print ( word "the convergence old_GT" old_GT "and new GT" new_GT)

;  show "-------------------------------------";
    ]
  show "====================Successfull convergence==============================="
end


to-report convergence [GT GT']
let converge false
  if abs(GT' - GT) <= Gamma
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
