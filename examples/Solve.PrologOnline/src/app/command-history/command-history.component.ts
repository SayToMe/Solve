import { Component, OnInit, Input } from '@angular/core';

@Component({
  selector: 'app-command-history',
  templateUrl: './command-history.component.html',
  styleUrls: ['./command-history.component.scss']
})
export class CommandHistoryComponent implements OnInit {
  @Input() history: string[] = [];

  constructor() { }

  ngOnInit() {
  }

}
