import { Component, OnInit, Output, EventEmitter, Input, HostListener } from '@angular/core';

@Component({
  selector: 'app-command-line',
  templateUrl: './command-line.component.html',
  styleUrls: ['./command-line.component.scss']
})
export class CommandLineComponent implements OnInit {
  @Input() line = '';

  @Output() commandRaised = new EventEmitter<string>();

  constructor() { }

  ngOnInit() {
  }

  onKeydown(key: KeyboardEvent) {
    console.log(key);
    if (key.keyCode === 13) {
      this.commandRaised.emit(this.line);
    }
  }
}
